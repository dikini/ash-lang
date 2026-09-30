import SourceScheduledInstalledSupport

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyFrames (unwindStore)
open ParameterSensitiveBoundary

structure InstallationState
    (operations : SourcePlannedTyping.Operations) (policy : Syntax.TicketPolicy)
    (contracts : SourcePlannedTyping.Contracts) (tables : CallableProtectionFrames.Tables)
    (families : SourceDependencyFrames.Families) (required : SourceContextualRechecking.Required)
    (outward : List Instance) (annotations : Nat → Option SourceDependencyCapture.Scope)
    (world ambient history : List Nat) (resumes disposals annotatedStore : RecursiveRequirements.Store) (budget : Footprint)
    (ports : OperationRows operations) (owners : ContractRows contracts)
    (emptyRows : EnvironmentRows (fun _ => none))
    (output : PlannedModeValue) (outputRows : ModeRowsValue output) (run : LexicalUnwind.UseRunState) : Prop
    extends ExecutableState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows run where
  installedSupport : Supported (stackView operations run.execution.machine.stack) ambient

theorem source_installation_ready
    (source : ExecutableSource ambient operations policy contracts tables families required outward actions annotations world history
      resumes annotatedStore budget ports owners emptyRows output outputRows machine) :
    InstallationReady operations ambient machine := by
  cases source with
  | eval site phaseAgreement rooted bound annotation checked bounded =>
    intro handler body tail same
    obtain ⟨expression, runtime, stack⟩ := Configuration.mk.inj (LexicalUnwind.Machine.eval.inj same)
    have current := site.current
    rw [expression] at current
    have support := admitted_handler_support current site.currentResource.reproof
    simpa only [stack] using support
  | unwind => intro handler body tail impossible; cases impossible

theorem InstallationState.transition_support
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows run)
    (step : LexicalUnwind.Transition run.execution.machine after created discharged) :
    Supported (stackView operations after.stack) ambient :=
  ParameterSensitiveBoundary.transition_support step state.installedSupport (source_installation_ready state.source)

theorem InstallationState.event_support
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows run)
    (event : LexicalUnwind.Event run.execution after) :
    Supported (stackView operations after.machine.stack) ambient := by
  cases event with
  | step transition fresh => exact state.transition_support transition


theorem InstallationState.focus
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨whole, runtimeScope, stack⟩, issued, completed⟩, actions⟩)
    (position : Focus whole child evaluationContext) :
    ∃ plain : PlainData, plain.context = evaluationContext ∧ plain.scope = runtimeScope ∧
      InstallationState operations policy contracts tables families required outward annotations world ambient history
        resumes disposals annotatedStore budget ports owners emptyRows output outputRows
        ⟨⟨.eval ⟨child, runtimeScope, .push (.plain plain) stack⟩, issued, completed⟩, actions⟩ := by
  obtain ⟨plain, context, scope, next⟩ := state.toExecutableState.focus position
  refine ⟨plain, context, scope, next, ?_⟩
  exact .push _ _ _ state.installedSupport (List.nil_subset _)

theorem InstallationState.computation
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval before, issued, completed⟩, actions⟩)
    (ready : RecursiveExpressions.Ready before.expression)
    (step : RawStep before after [] []) :
    LexicalUnwind.Event ⟨.eval before, issued, completed⟩ ⟨.eval after, issued, completed⟩ ∧
    InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval after, issued, completed⟩, actions⟩ := by
  obtain ⟨event, next⟩ := state.toExecutableState.computation ready step
  exact ⟨event, next, state.event_support event⟩

theorem InstallationState.plug
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨value, runtimeScope, .push (.plain plain) tail⟩, issued, completed⟩, actions⟩)
    (closed : ClosedValue value) :
    LexicalUnwind.Event
      ⟨.eval ⟨value, runtimeScope, .push (.plain plain) tail⟩, issued, completed⟩
      ⟨.eval ⟨plain.context.plug value, plain.scope, tail⟩, issued, completed⟩ ∧
    InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨plain.context.plug value, plain.scope, tail⟩, issued, completed⟩, actions⟩ := by
  obtain ⟨event, next⟩ := state.toExecutableState.plug closed
  exact ⟨event, next, state.event_support event⟩

theorem InstallationState.finish_normal_cleanup
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨.unit, runtimeScope, .push (.running action value closed) tail⟩, issued, completed⟩, actions⟩) :
    LexicalUnwind.Event
      ⟨.eval ⟨.unit, runtimeScope, .push (.running action value closed) tail⟩, issued, completed⟩
      ⟨.eval ⟨value, action.scope, tail⟩, issued, .cleanup action.identity :: completed⟩ ∧
    InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨value, action.scope, tail⟩, issued, .cleanup action.identity :: completed⟩, actions⟩ := by
  obtain ⟨event, next⟩ := state.toExecutableState.finish_normal_cleanup
  exact ⟨event, next, state.event_support event⟩

theorem InstallationState.start_normal_cleanup
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨value, runtimeScope, .push (.armed action) tail⟩, issued, completed⟩, actions⟩)
    (closed : ClosedValue value) :
    LexicalUnwind.Event
      ⟨.eval ⟨value, runtimeScope, .push (.armed action) tail⟩, issued, completed⟩
      ⟨.eval ⟨.app action.action .unit, .none, .push (.running action value closed) tail⟩, issued, completed⟩ ∧
    InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨.app action.action .unit, .none, .push (.running action value closed) tail⟩, issued, completed⟩, actions⟩ := by
  obtain ⟨event, next⟩ := state.toExecutableState.start_normal_cleanup closed
  exact ⟨event, next, state.event_support event⟩

theorem InstallationState.register_cleanup
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨.cleanup callback body, runtimeScope, stack⟩, issued, completed⟩, actions⟩)
    (isValue : callback.IsValue) (fresh : (issued ++ [Owner.cleanup identity]).Nodup) :
    ∃ action : ActionData,
      action.identity = identity ∧ action.action = callback ∧ action.scope = runtimeScope ∧
      LexicalUnwind.Event
        ⟨.eval ⟨.cleanup callback body, runtimeScope, stack⟩, issued, completed⟩
        ⟨.eval ⟨body, runtimeScope, .push (.armed action) stack⟩,
          issued ++ [Owner.cleanup identity], completed⟩ ∧
      InstallationState operations policy contracts tables families required outward annotations world ambient history
        resumes disposals annotatedStore budget ports owners emptyRows output outputRows
        ⟨⟨.eval ⟨body, runtimeScope, .push (.armed action) stack⟩,
          issued ++ [Owner.cleanup identity], completed⟩, actions⟩ := by
  obtain ⟨action, identityEq, actionEq, scopeEq, event, next⟩ := state.toExecutableState.register_cleanup isValue fresh
  exact ⟨action, identityEq, actionEq, scopeEq, event, next, state.event_support event⟩

theorem InstallationState.enter_resource
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨.resource binder initializer body, runtimeScope, stack⟩, issued, completed⟩, actions⟩)
    (isValue : initializer.IsValue) (fresh : identity ∉ world) :
    ∃ payload answer, initializer = .integer payload ∧
      LexicalUnwind.Event
        ⟨.eval ⟨.resource binder initializer body, runtimeScope, stack⟩, issued, completed⟩
        ⟨.eval ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), runtimeScope,
          .push (.cell identity payload runtimeScope answer) stack⟩,
          issued ++ [Owner.resource identity], completed⟩ ∧
      InstallationState operations policy contracts tables families required outward annotations (world ++ [identity]) ambient history
        resumes disposals annotatedStore budget ports owners emptyRows output outputRows
        ⟨⟨.eval ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), runtimeScope,
          .push (.cell identity payload runtimeScope answer) stack⟩,
          issued ++ [Owner.resource identity], completed⟩, actions⟩ := by
  obtain ⟨payload, answer, expressionEq, event, next⟩ := state.toExecutableState.enter_resource isValue fresh
  exact ⟨payload, answer, expressionEq, event, next, state.event_support event⟩

theorem InstallationState.install_handler_at
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨.handle (Instantiation.freezeEffect effect) code arms, runtimeScope, stack⟩, issued, completed⟩, actions⟩)
    (activation : Nat) (fresh : activation ∉ history) :
    ∃ handler : HandlerData, ∃ nextTables nextFamilies nextRequired,
      handler.activation = activation ∧ handler.activation ∉ history ∧ handler.scope = runtimeScope ∧ handler.effectInst = effect ∧ handler.clauses = arms ∧
      (∀ old, old.activation ∈ stack.erase.activations →
        tables old = nextTables old ∧ families old = nextFamilies old ∧ required old = nextRequired old) ∧
      LexicalUnwind.Event
        ⟨.eval ⟨.handle (Instantiation.freezeEffect effect) code arms, runtimeScope, stack⟩, issued, completed⟩
        ⟨.eval ⟨code, runtimeScope, .push (.handler handler) stack⟩, issued, completed⟩ ∧
      InstallationState operations policy contracts nextTables nextFamilies nextRequired outward annotations world ambient
        (history ++ [handler.activation]) resumes disposals annotatedStore budget ports owners emptyRows output outputRows
        ⟨⟨.eval ⟨code, runtimeScope, .push (.handler handler) stack⟩, issued, completed⟩, actions⟩ := by
  obtain ⟨handler, nextTables, nextFamilies, nextRequired, identity, fresh, scope, effect, clauses, agree, event, next⟩ :=
    state.toExecutableState.install_handler_at activation fresh
  exact ⟨handler, nextTables, nextFamilies, nextRequired, identity, fresh, scope, effect, clauses, agree,
    event, next, state.event_support event⟩

theorem InstallationState.install_handler
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨.handle (Instantiation.freezeEffect effect) code arms, runtimeScope, stack⟩, issued, completed⟩, actions⟩) :
    ∃ handler : HandlerData, ∃ nextTables nextFamilies nextRequired,
      handler.activation ∉ history ∧ handler.scope = runtimeScope ∧ handler.effectInst = effect ∧ handler.clauses = arms ∧
      (∀ old, old.activation ∈ stack.erase.activations →
        tables old = nextTables old ∧ families old = nextFamilies old ∧ required old = nextRequired old) ∧
      LexicalUnwind.Event
        ⟨.eval ⟨.handle (Instantiation.freezeEffect effect) code arms, runtimeScope, stack⟩, issued, completed⟩
        ⟨.eval ⟨code, runtimeScope, .push (.handler handler) stack⟩, issued, completed⟩ ∧
      InstallationState operations policy contracts nextTables nextFamilies nextRequired outward annotations world ambient
        (history ++ [handler.activation]) resumes disposals annotatedStore budget ports owners emptyRows output outputRows
        ⟨⟨.eval ⟨code, runtimeScope, .push (.handler handler) stack⟩, issued, completed⟩, actions⟩ := by
  obtain ⟨handler, nextTables, nextFamilies, nextRequired, fresh, scope, effect, clauses, agree, event, next⟩ :=
    state.toExecutableState.install_handler
  exact ⟨handler, nextTables, nextFamilies, nextRequired, fresh, scope, effect, clauses, agree,
    event, next, state.event_support event⟩

theorem InstallationState.leave_handler
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨value, runtimeScope, .push (.handler handler) tail⟩, issued, completed⟩, actions⟩)
    (closed : ClosedValue value) :
    LexicalUnwind.Event
      ⟨.eval ⟨value, runtimeScope, .push (.handler handler) tail⟩, issued, completed⟩
      ⟨.eval ⟨value, handler.scope, tail⟩, issued, completed⟩ ∧
    InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨value, handler.scope, tail⟩, issued, completed⟩, actions⟩ := by
  obtain ⟨event, next⟩ := state.toExecutableState.leave_handler closed
  exact ⟨event, next, state.event_support event⟩

theorem InstallationState.leave_clause
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨value, runtimeScope, .spent owner answer caller tail⟩, issued, completed⟩, actions⟩)
    (closed : ClosedValue value) :
    LexicalUnwind.Event
      ⟨.eval ⟨value, runtimeScope, .spent owner answer caller tail⟩, issued, completed⟩
      ⟨.eval ⟨value, caller, tail⟩, issued, completed⟩ ∧
    InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨value, caller, tail⟩, issued, completed⟩, actions⟩ := by
  obtain ⟨event, next⟩ := state.toExecutableState.leave_clause closed
  exact ⟨event, next, state.event_support event⟩

theorem InstallationState.close_value
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨value, runtimeScope, .push (.closing identity caller) tail⟩, issued, completed⟩, actions⟩)
    (closed : ClosedValue value) :
    LexicalUnwind.Event
      ⟨.eval ⟨value, runtimeScope, .push (.closing identity caller) tail⟩, issued, completed⟩
      ⟨.eval ⟨.unit, caller, tail⟩, issued, .close identity :: completed⟩ ∧
    InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨.unit, caller, tail⟩, issued, .close identity :: completed⟩, actions⟩ := by
  obtain ⟨event, next⟩ := state.toExecutableState.close_value closed
  exact ⟨event, next, state.event_support event⟩

theorem InstallationState.finish_close_unit
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨.unit, runtimeScope, .push (.closing identity caller) tail⟩, issued, completed⟩, actions⟩) :
    RawStep ⟨.unit, runtimeScope, .push (.closing identity caller) tail⟩ ⟨.unit, caller, tail⟩ [] [.close identity] ∧
    LexicalUnwind.Event
      ⟨.eval ⟨.unit, runtimeScope, .push (.closing identity caller) tail⟩, issued, completed⟩
      ⟨.eval ⟨.unit, caller, tail⟩, issued, .close identity :: completed⟩ ∧
    InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨.unit, caller, tail⟩, issued, .close identity :: completed⟩, actions⟩ := by
  obtain ⟨raw, event, next⟩ := state.toExecutableState.finish_close_unit
  exact ⟨raw, event, next, state.event_support event⟩

theorem InstallationState.retire_value
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨value, runtimeScope, .push (.retiring owner) tail⟩, issued, completed⟩, actions⟩)
    (closed : ClosedValue value) :
    LexicalUnwind.Event
      ⟨.eval ⟨value, runtimeScope, .push (.retiring owner) tail⟩, issued, completed⟩
      ⟨.eval ⟨value, runtimeScope, tail⟩, issued, .ticket owner :: completed⟩ ∧
    InstallationState operations policy contracts tables families required outward annotations world ambient history
      (RecursiveTransport.removeOwner owner resumes) (RecursiveTransport.removeOwner owner disposals)
      (RecursiveTransport.removeOwner owner annotatedStore) budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨value, runtimeScope, tail⟩, issued, .ticket owner :: completed⟩, actions⟩ := by
  obtain ⟨event, next⟩ := state.toExecutableState.retire_value closed
  exact ⟨event, next, state.event_support event⟩

theorem InstallationState.retire
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨.unit, runtimeScope, .push (.retiring owner) tail⟩, issued, completed⟩, actions⟩) :
    RawStep ⟨.unit, runtimeScope, .push (.retiring owner) tail⟩ ⟨.unit, runtimeScope, tail⟩ [] [.ticket owner] ∧
    LexicalUnwind.Event
      ⟨.eval ⟨.unit, runtimeScope, .push (.retiring owner) tail⟩, issued, completed⟩
      ⟨.eval ⟨.unit, runtimeScope, tail⟩, issued, .ticket owner :: completed⟩ ∧
    InstallationState operations policy contracts tables families required outward annotations world ambient history
      (RecursiveTransport.removeOwner owner resumes) (RecursiveTransport.removeOwner owner disposals)
      (RecursiveTransport.removeOwner owner annotatedStore) budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨.unit, runtimeScope, tail⟩, issued, .ticket owner :: completed⟩, actions⟩ := by
  obtain ⟨raw, event, next⟩ := state.toExecutableState.retire
  exact ⟨raw, event, next, state.event_support event⟩

theorem InstallationState.read_cell
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨.perform (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)),
        runtimeScope, beforeStack⟩, issued, completed⟩, actions⟩)
    (builtin : operations.erase.erase.ports (.cell identity) 0 = some (.reference identity, .integer))
    (selected : CellUpdate identity payload payload beforeStack afterStack) :
    InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨.integer payload, runtimeScope, afterStack⟩, issued, completed⟩, actions⟩ := by
  exact ⟨state.toExecutableState.read_cell builtin selected,
    state.transition_support (.evaluate (.readCell identity payload runtimeScope beforeStack afterStack selected) trivial)⟩

theorem InstallationState.write_cell
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨.perform (Instantiation.freezeEffect (.cell identity)) 1
        (.pair (.resourceRef (.activation identity)) (.integer new)), runtimeScope, beforeStack⟩,
        issued, completed⟩, actions⟩)
    (builtin : operations.erase.erase.ports (.cell identity) 1 = some (.product (.reference identity) .integer, .unit))
    (selected : CellUpdate identity old new beforeStack afterStack) :
    InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨.unit, runtimeScope, afterStack⟩, issued, completed⟩, actions⟩ := by
  exact ⟨state.toExecutableState.write_cell builtin selected,
    state.transition_support (.evaluate (.writeCell identity old new runtimeScope beforeStack afterStack selected) trivial)⟩

theorem InstallationState.start_unwind_cleanup
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.unwind runtimeScope (.push (.armed action) tail), issued, completed⟩, actions⟩) :
    LexicalUnwind.Event
      ⟨.unwind runtimeScope (.push (.armed action) tail), issued, completed⟩
      ⟨.eval ⟨.app action.action .unit, .none, .push (.unwinding action) tail⟩, issued, completed⟩ ∧
    InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨.app action.action .unit, .none, .push (.unwinding action) tail⟩,
        issued, completed⟩, actions⟩ := by
  obtain ⟨event, next⟩ := state.toExecutableState.start_unwind_cleanup
  exact ⟨event, next, state.event_support event⟩

theorem InstallationState.finish_unwind_cleanup
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨.unit, runtimeScope, .push (.unwinding action) tail⟩, issued, completed⟩, actions⟩) :
    LexicalUnwind.Event
      ⟨.eval ⟨.unit, runtimeScope, .push (.unwinding action) tail⟩, issued, completed⟩
      ⟨.unwind action.scope tail, issued, .cleanup action.identity :: completed⟩ ∧
    InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.unwind action.scope tail, issued, .cleanup action.identity :: completed⟩, actions⟩ := by
  obtain ⟨event, next⟩ := state.toExecutableState.finish_unwind_cleanup
  exact ⟨event, next, state.event_support event⟩

theorem InstallationState.finish_unwind_close
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.unwind runtimeScope (.push (.closing identity caller) tail), issued, completed⟩, actions⟩) :
    LexicalUnwind.Event
      ⟨.unwind runtimeScope (.push (.closing identity caller) tail), issued, completed⟩
      ⟨.eval ⟨.unit, caller, tail⟩, issued, .close identity :: completed⟩ ∧
    InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨.unit, caller, tail⟩, issued, .close identity :: completed⟩, actions⟩ := by
  obtain ⟨event, next⟩ := state.toExecutableState.finish_unwind_close
  exact ⟨event, next, state.event_support event⟩

theorem InstallationState.leave_resource
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨value, runtimeScope, .push (.cell identity payload caller answer) tail⟩, issued, completed⟩, actions⟩)
    (closed : ClosedValue value) :
    LexicalUnwind.Event
      ⟨.eval ⟨value, runtimeScope, .push (.cell identity payload caller answer) tail⟩, issued, completed⟩
      ⟨.eval ⟨value, caller, tail⟩, issued, .resource identity :: completed⟩ ∧
    InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.eval ⟨value, caller, tail⟩, issued, .resource identity :: completed⟩, actions⟩ := by
  obtain ⟨event, next⟩ := state.toExecutableState.leave_resource closed
  exact ⟨event, next, state.event_support event⟩

theorem InstallationState.resume_successor
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows (.value terminal) outputRows
      ⟨⟨.eval ⟨.resume binder operand, runtimeScope, stack⟩, issued, completed⟩, actions⟩)
    (closed : ClosedValue operand) :
    ∃ owner nextStack,
      LexicalUnwind.Event
        ⟨.eval ⟨.resume binder operand, runtimeScope, stack⟩, issued, completed⟩
        ⟨.eval ⟨operand, runtimeScope, nextStack⟩, issued, .ticket owner :: completed⟩ ∧
      InstallationState operations policy contracts tables families required outward annotations world ambient history
        (RecursiveTransport.removeOwner owner resumes) (RecursiveTransport.removeOwner owner disposals)
        (RecursiveTransport.removeOwner owner annotatedStore) budget ports owners emptyRows (.value terminal) outputRows
        ⟨⟨.eval ⟨operand, runtimeScope, nextStack⟩, issued, .ticket owner :: completed⟩, actions⟩ := by
  obtain ⟨owner, nextStack, event, next⟩ := state.toExecutableState.resume_successor closed
  exact ⟨owner, nextStack, event, next, state.event_support event⟩

theorem InstallationState.discard_successor
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows (.value terminal) outputRows
      ⟨⟨.eval ⟨.discard binder, runtimeScope, stack⟩, issued, completed⟩, actions⟩)
    (identity : Nat) (fresh : Owner.close identity ∉ issued) :
    ∃ owner nextStack,
      LexicalUnwind.Event
        ⟨.eval ⟨.discard binder, runtimeScope, stack⟩, issued, completed⟩
        ⟨.unwind runtimeScope nextStack, issued ++ [.close identity], .ticket owner :: completed⟩ ∧
      InstallationState operations policy contracts tables families required outward annotations world ambient history
        (RecursiveTransport.removeOwner owner resumes) (RecursiveTransport.removeOwner owner disposals)
        (RecursiveTransport.removeOwner owner annotatedStore) budget ports owners emptyRows (.value terminal) outputRows
        ⟨⟨.unwind runtimeScope nextStack, issued ++ [.close identity], .ticket owner :: completed⟩, actions⟩ := by
  obtain ⟨owner, nextStack, event, next⟩ := state.toExecutableState.discard_successor identity fresh
  exact ⟨owner, nextStack, event, next, state.event_support event⟩

theorem InstallationState.advance
    (state : InstallationState operations policy contracts tables families required outward annotations world ambient history
      resumes disposals annotatedStore budget ports owners emptyRows output outputRows
      ⟨⟨.unwind runtimeScope before, issued, completed⟩, actions⟩)
    (step : LexicalUnwind.Advance before after discharged) :
    InstallationState operations policy contracts tables families required outward annotations world ambient history
      (unwindStore before resumes) (unwindStore before disposals) (unwindStore before annotatedStore)
      budget ports owners emptyRows output outputRows
      ⟨⟨.unwind runtimeScope after, issued, discharged ++ completed⟩, actions⟩ := by
  exact ⟨state.toExecutableState.advance step, state.transition_support (.advance step)⟩

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.focus
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.computation
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.plug
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.finish_normal_cleanup
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.start_normal_cleanup
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.register_cleanup
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.enter_resource
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.install_handler
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.leave_handler
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.leave_clause
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.close_value
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.finish_close_unit
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.retire_value
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.retire
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.read_cell
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.write_cell
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.start_unwind_cleanup
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.finish_unwind_cleanup
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.finish_unwind_close
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.leave_resource
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.resume_successor
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.discard_successor
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.advance

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.source_installation_ready
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.transition_support
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.event_support

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.InstallationState.install_handler_at
