import GenerativeFrames

/-!
Joining recursive result certificates with current scoped joint validity.
Normal computation derives its access checks and preserves results on the same
machine step. Request admission and complete initial-program checking remain open.
-/

namespace Ash.OneShot.GenerativeProgress
open Instantiation ScopedExpressions ScopedExecution
open GenerativeResults (Derives)
open GenerativeFrames (ConfigurationReturns StackReturns)
open DeclarationResults (signature)
open ScopedTyping (resourceWorld resource_world_append)

/-- This records only the currently supported outer forms, not latent bodies. -/
def SupportedHead : Code → Prop
  | .app _ _ | .handle _ _ _ | .resume _ _ | .discard _ | .cleanup _ _ => False
  | _ => True

theorem supported_head (checked : Derives declarations environment world code bound) : SupportedHead code := by
  cases checked with
  | leaf shape closed checked => cases code <;> simp_all [SupportedHead, Code.IsValue]
  | pair | bind | branch | perform | resource => trivial

/-- A local boundary, not an initial admission rule. Selection follows the
    actual ordered cut, including a source handler overriding a builtin. -/
def NoSourceRequest (configuration : Configuration) : Prop :=
  ∀ requested operation operand capture tail handler,
    configuration.expression = .perform (freezeEffect requested) operation operand →
    operand.IsValue → ¬ HandlerCut requested configuration.stack capture tail handler

theorem nonrequest_boundary
    (notRequest : ∀ requested operation operand,
      configuration.expression ≠ .perform (freezeEffect requested) operation operand) :
    NoSourceRequest configuration := by
  intro requested operation operand capture tail handler same value cut
  exact notRequest requested operation operand same

theorem value_boundary (value : configuration.expression.IsValue) : NoSourceRequest configuration := by
  apply nonrequest_boundary
  intro requested operation operand same
  rw [same] at value
  cases value

theorem builtin_boundary (update : CellUpdate identity old new before after) :
    NoSourceRequest ⟨.perform (freezeEffect (.cell identity)) operation operand, scope, before⟩ := by
  intro requested operation' operand' capture tail handler same value cut
  have instanceEq := freeze_effect_injective (Code.perform.inj same).1
  subst requested
  exact cell_update_excludes_handler_cut update cut

theorem cell_update_preserves_results
    (update : CellUpdate identity old new before after)
    (checked : StackReturns declarations world before input output) :
    StackReturns declarations world after input output := by
  induction update generalizing input output with
  | hit => cases checked with
      | cell absent rest => exact .cell absent rest
  | push miss next ih => cases checked with
      | plain context rest => exact .plain context (ih rest)
      | cell absent rest => exact .cell absent (ih rest)
      | handler rest => exact .handler (ih rest)
  | live next ih => cases checked with
      | live port saved rest => exact .live port saved (ih rest)
  | spent next ih => cases checked with
      | spent rest => exact .spent (ih rest)

theorem return_access_checks
    (checked : ConfigurationReturns declarations world configuration output)
    (boundary : NoSourceRequest configuration) :
    AccessChecks configuration ambient := by
  obtain ⟨environment, bound, code, stack⟩ := checked
  constructor
  · intro identity payload answer savedScope scope value tail same closed
    rw [same] at code stack
    cases stack with
    | cell absent rest => exact fun member => absent (GenerativeResults.value_support code closed member)
  · intro requested operation operand scope whole cap tail handler same cut closed
    exact False.elim (boundary requested operation operand cap tail handler
      (congrArg Configuration.expression same) closed.1 (same.symm ▸ cut))
  · intro binder owner scope caller input answer front cap tail plan same resolve built
    rw [same] at code
    exact False.elim (supported_head code)

theorem configuration_world_mono
    (checked : ConfigurationReturns declarations world configuration output)
    (included : world ⊆ larger) : ConfigurationReturns declarations larger configuration output := by
  obtain ⟨environment, bound, code, stack⟩ := checked
  exact ⟨environment, bound, GenerativeResults.world_mono code included, GenerativeFrames.stack_world_mono stack included⟩

/-- Arbitrary raw annotations do not establish joint typing. This theorem
    preserves the result component; the progress join below constructs typing. -/
theorem raw_preserves_results
    (step : RawStep before after created discharged)
    (fresh : (issued ++ created).Nodup)
    (checked : ConfigurationReturns declarations (resourceWorld issued) before output)
    (boundary : NoSourceRequest before) :
    ConfigurationReturns declarations (resourceWorld (issued ++ created)) after output := by
  cases step with
  | focus plain focus tail =>
      simpa using (GenerativeFrames.focus_step focus checked).2
  | plug plain value closed scope tail =>
      simpa using (GenerativeFrames.plug_step checked closed).2
  | bind name value body scope tail closed suffix =>
      simpa using (GenerativeFrames.bind_step checked closed suffix).2
  | beta | enterHandler | enterCleanup | resume | discard =>
      obtain ⟨environment, bound, code, stack⟩ := checked
      exact False.elim (supported_head code)
  | ifTrue yes no scope tail =>
      obtain ⟨environment, bound, code, stack⟩ := checked
      cases code with
      | leaf shape closed finite => simp [Code.IsValue] at shape
      | branch condition yesChecked noChecked => exact ⟨environment, bound, by simpa using yesChecked, by simpa using stack⟩
  | ifFalse yes no scope tail =>
      obtain ⟨environment, bound, code, stack⟩ := checked
      cases code with
      | leaf shape closed finite => simp [Code.IsValue] at shape
      | branch condition yesChecked noChecked => exact ⟨environment, bound, by simpa using noChecked, by simpa using stack⟩
  | leaveHandler handler value closed scope tail =>
      simpa using (GenerativeFrames.handler_return_step checked closed).2
  | enterCell binder identity payload body scope answer tail closed =>
      have unused : identity ∉ resourceWorld issued := by
        intro member
        exact (List.nodup_append.mp fresh).2.2 (.resource identity)
          (ScopedTyping.mem_resource_world.mp member) (.resource identity) (by simp) rfl
      simpa [resource_world_append, resourceWorld] using (GenerativeFrames.resource_step checked unused).2
  | leaveCell identity payload answer savedScope scope value closed tail =>
      simpa using (GenerativeFrames.cell_return_step (ambient := []) checked closed).2.2
  | startCleanup | finishCleanup | finishClose | retire =>
      obtain ⟨environment, bound, code, stack⟩ := checked
      cases stack
  | capture requested operation parameter binder owner operand body scope whole cap tail handler answer cut clause closed ready =>
      exact False.elim (boundary requested operation operand cap tail handler rfl closed.1 cut)
  | leaveClause owner answer value closed scope caller tail =>
      obtain ⟨environment, bound, code, stack⟩ := checked
      cases stack with
      | spent rest => exact ⟨environment, bound, by simpa using code, by simpa using rest⟩
  | readCell identity payload scope before after selected =>
      obtain ⟨environment, bound, code, stack⟩ := checked
      have closed : ClosedValue (.integer payload) := ⟨trivial, rfl, by intro dependency member; cases member⟩
      exact ⟨environment, bound, .leaf (Or.inl trivial) rfl
        (GenerativeFrames.closed_value_check closed (List.nil_subset _)),
        by simpa using cell_update_preserves_results selected stack⟩
  | writeCell identity old new scope before after selected =>
      obtain ⟨environment, bound, code, stack⟩ := checked
      have closed : ClosedValue .unit := ⟨trivial, rfl, by intro dependency member; cases member⟩
      exact ⟨environment, bound, .leaf (Or.inl trivial) rfl
        (GenerativeFrames.closed_value_check closed (List.nil_subset _)),
        by simpa using cell_update_preserves_results selected stack⟩

theorem named_preserves_results
    (step : NamedAccessStep ambient before after)
    (checked : ConfigurationReturns declarations (resourceWorld before.execution.issued) before.execution.configuration output)
    (boundary : NoSourceRequest before.execution.configuration) :
    ConfigurationReturns declarations (resourceWorld after.execution.issued) after.execution.configuration output := by
  cases step.execution with
  | event after created discharged raw fresh freshHandlers => exact raw_preserves_results raw fresh checked boundary

theorem boundary_allocates_no_ticket
    (step : RawStep before after created discharged) (boundary : NoSourceRequest before) :
    ∀ owner, Owner.ticket owner ∉ created := by
  cases step <;> try { intro owner; simp }
  rename_i requested operation parameter binder owner operand body scope whole cap tail handler output cut clause closed environment
  exact False.elim (boundary requested operation operand cap tail handler rfl closed.1 cut)

theorem boundary_named_registry_unchanged
    (step : NamedAccessStep ambient before after)
    (beforeHistory : ScopedPortJoint.RegistryHistory registry before.execution.issued)
    (afterHistory : ScopedPortJoint.RegistryHistory nextRegistry after.execution.issued)
    (extension : ScopedPortProgress.RegistryExtends registry nextRegistry)
    (boundary : NoSourceRequest before.execution.configuration) : registry = nextRegistry := by
  cases step.execution with
  | event after created discharged raw fresh freshHandlers =>
      exact ScopedPortPrepared.registry_unchanged_without_ticket_allocation beforeHistory afterHistory extension
        (boundary_allocates_no_ticket raw boundary)

theorem boundary_preserves_closing
    (step : NamedAccessStep ambient before after)
    (checked : ScopedPortProgress.ClosingInterfaces ports (resourceWorld before.execution.issued) registry
      before.execution.configuration.stack)
    (boundary : NoSourceRequest before.execution.configuration) :
    ScopedPortProgress.ClosingInterfaces ports (resourceWorld after.execution.issued) registry
      after.execution.configuration.stack := by
  cases step.execution with
  | event after created discharged raw fresh freshHandlers =>
      exact ScopedPortPrepared.raw_step_preserves_closing_interfaces raw checked
        (ScopedPortProgress.registry_extends_refl _)
        (by rw [resource_world_append]; exact List.subset_append_left _ _)
        (.none (boundary_allocates_no_ticket raw boundary))

/-- The same generated event preserves joint validity, historical closing
    interfaces and result bounds. The local boundary need not survive it. -/
theorem current_progress
    (ready : ScopedPortPrepared.Ready (signature declarations) policy registry ambient before result outgoing)
    (checked : ConfigurationReturns declarations (resourceWorld before.execution.issued) before.execution.configuration output)
    (boundary : NoSourceRequest before.execution.configuration) :
    ScopedPortProgress.Terminal before.execution.configuration ∨
      ScopedPortProgress.OutwardRequest before.execution.configuration outgoing ∨ ∃ after,
      NamedAccessStep ambient before after ∧
      ScopedPortPrepared.Ready (signature declarations) policy registry ambient after result outgoing ∧
      ConfigurationReturns declarations (resourceWorld after.execution.issued) after.execution.configuration output := by
  rcases ScopedPortProgress.current_progress ready.joint ready.closing (return_access_checks checked boundary) with terminal | outward | next
  · exact Or.inl terminal
  · exact Or.inr (Or.inl outward)
  · obtain ⟨nextRegistry, after, step, afterValid, extension⟩ := next
    have same := boundary_named_registry_unchanged step ready.joint.registry afterValid.registry extension boundary
    subst nextRegistry
    exact Or.inr (Or.inr ⟨after, step, ⟨afterValid, boundary_preserves_closing step ready.closing boundary⟩,
      named_preserves_results step checked boundary⟩)

theorem nonrequest_progress
    (ready : ScopedPortPrepared.Ready (signature declarations) policy registry ambient before result outgoing)
    (checked : ConfigurationReturns declarations (resourceWorld before.execution.issued) before.execution.configuration output)
    (notRequest : ∀ requested operation operand,
      before.execution.configuration.expression ≠ .perform (freezeEffect requested) operation operand) :
    ScopedPortProgress.Terminal before.execution.configuration ∨ ∃ after,
      NamedAccessStep ambient before after ∧
      ScopedPortPrepared.Ready (signature declarations) policy registry ambient after result outgoing ∧
      ConfigurationReturns declarations (resourceWorld after.execution.issued) after.execution.configuration output := by
  rcases current_progress ready checked (nonrequest_boundary notRequest) with terminal | outward | next
  · exact Or.inl terminal
  · obtain ⟨requested, operation, operand, same, value, exported, missing⟩ := outward
    exact False.elim (notRequest requested operation operand same)
  · exact Or.inr next

theorem value_progress
    (ready : ScopedPortPrepared.Ready (signature declarations) policy registry ambient before result outgoing)
    (checked : ConfigurationReturns declarations (resourceWorld before.execution.issued) before.execution.configuration output)
    (value : before.execution.configuration.expression.IsValue) :
    ScopedPortProgress.Terminal before.execution.configuration ∨ ∃ after,
      NamedAccessStep ambient before after ∧
      ScopedPortPrepared.Ready (signature declarations) policy registry ambient after result outgoing ∧
      ConfigurationReturns declarations (resourceWorld after.execution.issued) after.execution.configuration output := by
  apply nonrequest_progress ready checked
  intro requested operation operand same
  rw [same] at value
  cases value

theorem closed_progress
    (ready : ScopedPortPrepared.Ready (signature declarations) policy registry ambient before result [])
    (checked : ConfigurationReturns declarations (resourceWorld before.execution.issued) before.execution.configuration output)
    (boundary : NoSourceRequest before.execution.configuration) :
    ScopedPortProgress.Terminal before.execution.configuration ∨ ∃ after,
      NamedAccessStep ambient before after ∧
      ScopedPortPrepared.Ready (signature declarations) policy registry ambient after result [] ∧
      ConfigurationReturns declarations (resourceWorld after.execution.issued) after.execution.configuration output := by
  rcases current_progress ready checked boundary with terminal | outward | next
  · exact Or.inl terminal
  · obtain ⟨requested, operation, operand, same, value, impossible, missing⟩ := outward
    cases impossible
  · exact Or.inr next

/-- Initial typing, usage and stored-result checks derive the first step.
    They do not establish admission of a later selected handler clause. -/
theorem initial_progress
    (typed : ScopedPorts.Typed (signature declarations) [] ScopedPorts.TypeEnv.empty .none [] expression result)
    (used : Uses policy .none .available expression .available)
    (support : Syntax.resourceDependencies expression.dependencies = [])
    (bounded : Derives declarations (fun _ => .unknown) [] expression output) :
    expression.IsValue ∨ ∃ after,
      NamedAccessStep [] ⟨⟨⟨expression, .none, .nil⟩, [], []⟩, []⟩ after ∧
      ScopedPortPrepared.Ready (signature declarations) policy (fun _ => none) [] after result [] ∧
      ConfigurationReturns declarations (resourceWorld after.execution.issued) after.execution.configuration output := by
  have ready := ScopedPortPrepared.initial_ready typed used support
  have checked : ConfigurationReturns declarations [] ⟨expression, .none, .nil⟩ output :=
    ⟨_, output, bounded, .nil⟩
  have boundary : NoSourceRequest ⟨expression, .none, .nil⟩ := by
    intro requested operation operand capture tail handler same value cut
    cases cut
  rcases closed_progress ready checked boundary with terminal | next
  · exact Or.inl terminal.1
  · exact Or.inr next

namespace Examples
open GenerativeFrames.Examples (declarations environment answer)

theorem ordinary_initial_progress : ∃ after,
    NamedAccessStep [] ⟨⟨GenerativeFrames.Examples.s0, [], []⟩, []⟩ after ∧
    ScopedPortPrepared.Ready (signature declarations) GenerativeFrames.Examples.policy (fun _ => none) [] after
      (ScopedPorts.eraseType answer) [] ∧
    ConfigurationReturns declarations (resourceWorld after.execution.issued) after.execution.configuration [] := by
  rcases initial_progress GenerativeFrames.Examples.program_typed
    (.bind (.bind .integer (.resource .integer (.resource .integer (.lambda .integer)))) .variable)
    rfl GenerativeFrames.Examples.program_bound with terminal | next
  · cases terminal
  · exact next

def readStack : Stack := OperationReturns.Examples.readStack
def reading : Configuration := OperationReturns.Examples.reading
def readResult : Configuration := OperationReturns.Examples.readResult

theorem reading_returns : ConfigurationReturns declarations [7] reading [] := by
  refine ⟨environment, [], .perform (operandBound := [7]) (.leaf (Or.inl trivial) rfl rfl) rfl rfl, ?_⟩
  exact .plain (environment := environment) (.bind (.leaf (Or.inl trivial) rfl rfl)) (.cell (by simp) .nil)

theorem builtin_read_results : RawStep reading readResult [] [] ∧
    NoSourceRequest reading ∧ ConfigurationReturns declarations [7] readResult [] := by
  have update : CellUpdate 7 41 41 readStack readStack := .push (by decide) .hit
  have raw : RawStep reading readResult [] [] := .readCell 7 41 .none readStack readStack update
  have boundary : NoSourceRequest reading := builtin_boundary update
  exact ⟨raw, boundary, raw_preserves_results (issued := [.resource 7]) raw (by decide) reading_returns boundary⟩

def waitingRequest : PlainData :=
  ⟨.perform (freezeEffect ContinuationBounds.Examples.family) 0, .none, .unit, .integer, [], rfl⟩
def beforeRequest : Configuration :=
  ⟨.unit, .none, .push (.plain waitingRequest) ContinuationBounds.Examples.saved⟩

theorem ready_source_request_rejected : ¬ NoSourceRequest ContinuationBounds.Examples.requesting := by
  intro boundary
  exact boundary ContinuationBounds.Examples.family 0 .unit _ _ _ rfl trivial ContinuationBounds.Examples.saved_cut

theorem boundary_need_not_survive_plug :
    NoSourceRequest beforeRequest ∧ ConfigurationReturns declarations [7] beforeRequest [] ∧
    RawStep beforeRequest ContinuationBounds.Examples.requesting [] [] ∧
    ConfigurationReturns declarations [7] ContinuationBounds.Examples.requesting [] ∧
    ¬ NoSourceRequest ContinuationBounds.Examples.requesting := by
  have closed : ClosedValue Code.unit := ⟨trivial, rfl, by intro dependency member; cases member⟩
  have checked : ConfigurationReturns declarations [7] beforeRequest [] :=
    ⟨environment, [], .leaf (Or.inl trivial) rfl rfl,
      .plain (environment := environment) (.perform rfl rfl) GenerativeFrames.Examples.saved_capture_returns⟩
  have step := GenerativeFrames.plug_step checked closed
  exact ⟨value_boundary trivial, checked, step.1, step.2, ready_source_request_rejected⟩

def reusedBefore : Configuration := ⟨.resource 4 (.integer 0) (.resourceRef (.activation 8)), .none, .nil⟩
def reusedAfter : Configuration := ⟨.resourceRef (.activation 8), .none, .push (.cell 8 0 .none (.reference 8)) .nil⟩

theorem freshness_is_necessary :
    ConfigurationReturns declarations [8] reusedBefore [8] ∧
    RawStep reusedBefore reusedAfter [.resource 8] [] ∧
    ¬ ConfigurationReturns declarations [8, 8] reusedAfter [8] := by
  have checked : ConfigurationReturns declarations [8] reusedBefore [8] := by
    refine ⟨environment, [8], ?_, .nil⟩
    exact .resource (initializerBound := []) (.leaf (Or.inl trivial) rfl rfl) rfl
      (fun identity fresh => .leaf (Or.inl trivial) rfl rfl) (List.Subset.refl _)
  refine ⟨checked, .enterCell 4 8 0 (.resourceRef (.activation 8)) .none (.reference 8) .nil rfl, ?_⟩
  intro after
  obtain ⟨environment, bound, code, stack⟩ := after
  cases stack with
  | cell absent rest =>
      have closed : ClosedValue (Code.resourceRef (.activation 8)) :=
        ⟨trivial, rfl, by
          intro dependency member
          have same : dependency = Syntax.Dependency.resource 8 := by simpa [Code.dependencies] using member
          cases same
          trivial⟩
      exact absent (GenerativeResults.value_support code closed (a := 8) (by decide))

end Examples

end Ash.OneShot.GenerativeProgress

#print axioms Ash.OneShot.GenerativeProgress.supported_head
#print axioms Ash.OneShot.GenerativeProgress.nonrequest_boundary
#print axioms Ash.OneShot.GenerativeProgress.value_boundary
#print axioms Ash.OneShot.GenerativeProgress.builtin_boundary
#print axioms Ash.OneShot.GenerativeProgress.cell_update_preserves_results
#print axioms Ash.OneShot.GenerativeProgress.return_access_checks
#print axioms Ash.OneShot.GenerativeProgress.configuration_world_mono
#print axioms Ash.OneShot.GenerativeProgress.raw_preserves_results
#print axioms Ash.OneShot.GenerativeProgress.named_preserves_results
#print axioms Ash.OneShot.GenerativeProgress.boundary_allocates_no_ticket
#print axioms Ash.OneShot.GenerativeProgress.boundary_named_registry_unchanged
#print axioms Ash.OneShot.GenerativeProgress.boundary_preserves_closing
#print axioms Ash.OneShot.GenerativeProgress.current_progress
#print axioms Ash.OneShot.GenerativeProgress.nonrequest_progress
#print axioms Ash.OneShot.GenerativeProgress.value_progress
#print axioms Ash.OneShot.GenerativeProgress.closed_progress
#print axioms Ash.OneShot.GenerativeProgress.initial_progress
#print axioms Ash.OneShot.GenerativeProgress.Examples.ordinary_initial_progress
#print axioms Ash.OneShot.GenerativeProgress.Examples.reading_returns
#print axioms Ash.OneShot.GenerativeProgress.Examples.builtin_read_results
#print axioms Ash.OneShot.GenerativeProgress.Examples.ready_source_request_rejected
#print axioms Ash.OneShot.GenerativeProgress.Examples.boundary_need_not_survive_plug
#print axioms Ash.OneShot.GenerativeProgress.Examples.freshness_is_necessary
