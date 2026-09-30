import SourceScheduledPreservationState

/-! Constructive preservation for allocation and continuation-use requests.
Requests describe only the predecessor and operational inputs. Results record
chosen metadata separately from the complete successor invariant. -/
namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.Allocating
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Contract)
open RecursiveRequirements (Requirements)

/-- The seven endpoint families whose output contains source-selected data. -/
inductive Request (before : Snapshot operations) : Type where
  | focus
      (shape : before.run = ⟨⟨.eval ⟨whole, runtimeScope, stack⟩, issued, completed⟩, actions⟩)
      (position : Focus whole child evaluationContext) : Request before
  | registerCleanup
      (shape : before.run = ⟨⟨.eval ⟨.cleanup callback body, runtimeScope, stack⟩, issued, completed⟩, actions⟩)
      (isValue : callback.IsValue) (fresh : (issued ++ [Owner.cleanup identity]).Nodup) : Request before
  | enterResource
      (shape : before.run = ⟨⟨.eval ⟨.resource binder initializer body, runtimeScope, stack⟩, issued, completed⟩, actions⟩)
      (isValue : initializer.IsValue) (fresh : identity ∉ before.world) : Request before
  | installHandler
      (shape : before.run = ⟨⟨.eval ⟨.handle (Instantiation.freezeEffect effect) body arms, runtimeScope, stack⟩,
        issued, completed⟩, actions⟩) : Request before
  | capture
      (shape : before.run = ⟨⟨.eval ⟨.perform (Instantiation.freezeEffect effect) operation operand, runtimeScope, stack⟩,
        issued, completed⟩, actions⟩)
      (physical : HandlerCut effect stack capturedStack tailStack handler)
      (closed : ClosedValue operand) (owner : Nat) (fresh : (issued ++ [Owner.ticket owner]).Nodup)
      (resumeRow : Footprint) (closeRow : Option Footprint) : Request before
  | resume
      (shape : before.run = ⟨⟨.eval ⟨.resume binder operand, runtimeScope, stack⟩, issued, completed⟩, actions⟩)
      (closed : ClosedValue operand) : Request before
  | discard
      (shape : before.run = ⟨⟨.eval ⟨.discard binder, runtimeScope, stack⟩, issued, completed⟩, actions⟩)
      (identity : Nat) (fresh : Owner.close identity ∉ issued) : Request before

/-- Chosen metadata and bookkeeping, without successor validity premises.
Capture retains the public M1 result; the accompanying event witnesses its
operational target, and this relation records every evolving static field. -/
inductive Realizes {before : Snapshot operations} : Request before → Snapshot operations → Prop where
  | focus {shape : before.run = ⟨⟨.eval ⟨whole, runtimeScope, stack⟩, issued, completed⟩, actions⟩}
      {position : Focus whole child evaluationContext} (plain : PlainData)
      (context : plain.context = evaluationContext) (scope : plain.scope = runtimeScope) :
      Realizes (.focus shape position) { before with
        run := ⟨⟨.eval ⟨child, runtimeScope, .push (.plain plain) stack⟩, issued, completed⟩, actions⟩ }
  | registerCleanup
      {shape : before.run = ⟨⟨.eval ⟨.cleanup callback body, runtimeScope, stack⟩, issued, completed⟩, actions⟩}
      {isValue : callback.IsValue} {fresh : (issued ++ [Owner.cleanup identity]).Nodup}
      (action : ActionData) (identityEq : action.identity = identity)
      (actionEq : action.action = callback) (scopeEq : action.scope = runtimeScope) :
      Realizes (.registerCleanup shape isValue fresh) { before with
        run := ⟨⟨.eval ⟨body, runtimeScope, .push (.armed action) stack⟩,
          issued ++ [.cleanup identity], completed⟩, actions⟩ }
  | enterResource
      {shape : before.run = ⟨⟨.eval ⟨.resource binder initializer body, runtimeScope, stack⟩, issued, completed⟩, actions⟩}
      {isValue : initializer.IsValue} {fresh : identity ∉ before.world}
      (payload : Int) (answer : Ty) (expressionEq : initializer = .integer payload) :
      Realizes (.enterResource shape isValue fresh) { before with
        world := before.world ++ [identity]
        run := ⟨⟨.eval ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), runtimeScope,
          .push (.cell identity payload runtimeScope answer) stack⟩,
          issued ++ [.resource identity], completed⟩, actions⟩ }
  | installHandler
      {shape : before.run = ⟨⟨.eval ⟨.handle (Instantiation.freezeEffect effect) body arms, runtimeScope, stack⟩,
        issued, completed⟩, actions⟩}
      (handler : HandlerData) (nextTables : CallableProtectionFrames.Tables)
      (nextFamilies : SourceDependencyFrames.Families) (nextRequired : SourceContextualRechecking.Required)
      (fresh : handler.activation ∉ before.history) (scope : handler.scope = runtimeScope)
      (effectEq : handler.effectInst = effect) (clauses : handler.clauses = arms)
      (agree : ∀ old, old.activation ∈ stack.erase.activations →
        before.tables old = nextTables old ∧ before.families old = nextFamilies old ∧ before.required old = nextRequired old) :
      Realizes (.installHandler shape) { before with
        tables := nextTables
        families := nextFamilies
        required := nextRequired
        history := before.history ++ [handler.activation]
        run := ⟨⟨.eval ⟨body, runtimeScope, .push (.handler handler) stack⟩, issued, completed⟩, actions⟩ }
  | capture
      {shape : before.run = ⟨⟨.eval ⟨.perform (Instantiation.freezeEffect effect) operation operand, runtimeScope, stack⟩,
        issued, completed⟩, actions⟩}
      {physical : HandlerCut effect stack capturedStack tailStack handler}
      {closed : ClosedValue operand} {owner : Nat} {fresh : (issued ++ [Owner.ticket owner]).Nodup}
      {resumeRow : Footprint} {closeRow : Option Footprint}
      (allocated : Contract) (inputRows : ValueRows allocated.input) (answerRows : ValueRows allocated.answer)
      (captureScope : SourceDependencyCapture.Scope) (saved : Requirements allocated.resumeDemand)
      (rights : Syntax.OneShotRights) (next : Configuration) :
      Realizes (.capture shape physical closed owner fresh resumeRow closeRow) { before with
        contracts := before.contracts.insert owner allocated
        owners := before.owners.insert owner inputRows answerRows
        annotations := fun other => if other = owner then some captureScope else before.annotations other
        resumes := (⟨owner, .resume⟩, ⟨allocated.resumeDemand, saved⟩) :: before.resumes
        annotatedStore := (⟨owner, .resume⟩, ⟨allocated.resumeDemand, saved⟩) :: before.annotatedStore
        run := ⟨⟨.eval next, issued ++ [.ticket owner], completed⟩, actions.insert owner rights⟩ }
  | resume
      {shape : before.run = ⟨⟨.eval ⟨.resume binder operand, runtimeScope, stack⟩, issued, completed⟩, actions⟩}
      {closed : ClosedValue operand} (owner : Nat) (nextStack : Stack) :
      Realizes (.resume shape closed) { before with
        resumes := RecursiveTransport.removeOwner owner before.resumes
        disposals := RecursiveTransport.removeOwner owner before.disposals
        annotatedStore := RecursiveTransport.removeOwner owner before.annotatedStore
        run := ⟨⟨.eval ⟨operand, runtimeScope, nextStack⟩, issued, .ticket owner :: completed⟩, actions⟩ }
  | discard
      {shape : before.run = ⟨⟨.eval ⟨.discard binder, runtimeScope, stack⟩, issued, completed⟩, actions⟩}
      {identity : Nat} {fresh : Owner.close identity ∉ issued} (owner : Nat) (nextStack : Stack) :
      Realizes (.discard shape identity fresh) { before with
        resumes := RecursiveTransport.removeOwner owner before.resumes
        disposals := RecursiveTransport.removeOwner owner before.disposals
        annotatedStore := RecursiveTransport.removeOwner owner before.annotatedStore
        run := ⟨⟨.unwind runtimeScope nextStack, issued ++ [.close identity], .ticket owner :: completed⟩, actions⟩ }

/-- Every operational request has a concrete event and a complete successor.
The existential metadata is chosen by the existing source-derived M1 endpoint. -/
theorem Request.preserve {operations : Operations} {before : Snapshot operations}
    {policy : Syntax.TicketPolicy} {outward : List Instance} {ambient : List Nat}
    {budget : Footprint} {ports : OperationRows operations}
    {emptyRows : EnvironmentRows (fun _ => none)}
    {output : SourcePlannedTyping.Value} {outputRows : ValueRows output}
    (valid : Valid (operations := operations) policy outward ambient budget ports emptyRows output outputRows before)
    (request : Request before) :
    ∃ after, LexicalUnwind.Event before.run.execution after.run.execution ∧
      Realizes request after ∧ Valid (operations := operations) policy outward ambient budget ports emptyRows output outputRows after := by
  have state := valid.unpack
  cases request with
  | focus shape position =>
    rename_i whole runtimeScope stack issued completed actions child evaluationContext
    rw [shape] at state
    obtain ⟨plain, context, scope, next⟩ := state.focus position
    have raw := RawStep.focus plain (context.symm ▸ position) stack
    have transition := LexicalUnwind.UseTransition.evaluate raw
      (LexicalUnwind.focus_computation_head (context.symm ▸ position))
    rw [scope] at transition
    have event := LexicalUnwind.Event.step
      (before := ⟨.eval ⟨whole, runtimeScope, stack⟩, issued, completed⟩) transition.erases
      (by simpa only [List.append_nil, LexicalUnwind.RunState.erase] using state.ledger.2)
    refine ⟨Snapshot.ofState next, ?_, .focus plain context scope, valid_ofState next⟩
    simpa only [shape, Snapshot.ofState_run, List.append_nil, List.nil_append] using event
  | registerCleanup shape isValue fresh =>
    rw [shape] at state
    obtain ⟨action, identityEq, actionEq, scopeEq, event, next⟩ := state.register_cleanup isValue fresh
    refine ⟨Snapshot.ofState next, ?_, .registerCleanup action identityEq actionEq scopeEq, valid_ofState next⟩
    simpa only [shape, Snapshot.ofState_run] using event
  | enterResource shape isValue fresh =>
    rw [shape] at state
    obtain ⟨payload, answer, expressionEq, event, next⟩ := state.enter_resource isValue fresh
    refine ⟨Snapshot.ofState next, ?_, .enterResource payload answer expressionEq, valid_ofState next⟩
    simpa only [shape, Snapshot.ofState_run] using event
  | installHandler shape =>
    rw [shape] at state
    obtain ⟨handler, tables, families, required, fresh, scope, effectEq, clauses, agree, event, next⟩ := state.install_handler
    refine ⟨Snapshot.ofState next, ?_, .installHandler handler tables families required fresh scope effectEq clauses agree,
      valid_ofState next⟩
    simpa only [shape, Snapshot.ofState_run] using event
  | capture shape physical closed owner fresh resumeRow closeRow =>
    rw [shape] at state
    obtain ⟨allocated, inputRows, answerRows, captureScope, saved, rights, configuration, event, next⟩ :=
      state.capture_successor physical closed owner fresh resumeRow closeRow
    refine ⟨Snapshot.ofState next, ?_, .capture allocated inputRows answerRows captureScope saved rights configuration,
      valid_ofState next⟩
    simpa only [shape, Snapshot.ofState_run] using event
  | resume shape closed =>
    rw [shape] at state
    obtain ⟨owner, nextStack, event, next⟩ := state.resume_successor closed
    refine ⟨Snapshot.ofState next, ?_, .resume owner nextStack, valid_ofState next⟩
    simpa only [shape, Snapshot.ofState_run] using event
  | discard shape identity fresh =>
    rw [shape] at state
    obtain ⟨owner, nextStack, event, next⟩ := state.discard_successor identity fresh
    refine ⟨Snapshot.ofState next, ?_, .discard owner nextStack, valid_ofState next⟩
    simpa only [shape, Snapshot.ofState_run] using event

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.Allocating

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.Allocating.Request.preserve
