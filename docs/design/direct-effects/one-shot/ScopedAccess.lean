import ScopedNames
import ScopedDependencies

/-!
Live resource support for scoped execution. Local checks inspect release,
selected capture payloads, and structural closing plans. This layer derives
post-state support from those checks and the initial invariant; complete source
admission and progress remain separate obligations.
-/

namespace Ash.OneShot.ScopedExecution
open Instantiation ScopedExpressions
open Syntax (Dependency resourceDependencies mem_resourceDependencies mem_without without)
open Execution (visible_resource_owned retainedResources retained_resource_supported)

theorem start_cleanup_preserves_retained_support
    {action : ActionData} {tail : Stack}
    (support : Supported (.push action.erase tail.erase) ambient)
    (closed : ClosedValue saved)
    (savedSupported : resourceDependencies saved.dependencies ⊆ tail.erase.visible ++ ambient) :
    Supported (.push (ExecFrame.erase (.running action saved closed)) tail.erase) ambient := by
  cases support with
  | push frame rest ambient next access =>
      apply Supported.push _ _ _ next
      intro resource retained
      rcases List.mem_append.mp retained with inAction | inSaved
      · exact access inAction
      · exact savedSupported inSaved

structure AccessValid (configuration : Configuration) (ambient : List Nat) : Prop where
  control : Supported configuration.stack.erase ambient
  expression : resourceDependencies configuration.expression.dependencies ⊆
    configuration.stack.erase.visible ++ ambient

/-- Three local checks beyond raw execution: no released resource in the
    returned value, outward support of a captured request's operand, and the
    structural disposal judgment for the actual cut and surviving control. -/
structure AccessChecks (before : Configuration) (ambient : List Nat) : Prop where
  release : ∀ identity payload answer savedScope scope value tail,
    before = ⟨value, scope, .push (.cell identity payload savedScope answer) tail⟩ →
    ClosedValue value → identity ∉ resourceDependencies value.dependencies
  capture : ∀ requested operation operand scope whole cap tail handler,
    before = ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ →
    HandlerCut requested whole cap tail handler → ClosedValue operand →
    resourceDependencies operand.dependencies ⊆ tail.erase.visible ++ ambient
  discard : ∀ binder ticket scope callerScope q answer (front cap tail : Stack) plan,
    before = ⟨.discard binder, scope, front.append (.live ticket q answer cap callerScope tail)⟩ →
    scope.resolve binder = some ticket → makePlan cap = some plan →
    Discardable cap.erase (front.erase.append (.spent ticket answer tail.erase))
      (plan.map CloseEntry.erase)

@[simp] theorem resource_dependencies_append (left right : List Dependency) :
    resourceDependencies (left ++ right) = resourceDependencies left ++ resourceDependencies right := by
  simp [resourceDependencies]

theorem context_dependency_membership (context : Context) (expression : Code) (dependency : Dependency) :
    dependency ∈ (context.plug expression).dependencies ↔
      dependency ∈ context.dependencies ∨ dependency ∈ expression.dependencies := by
  cases context <;> simp [Context.dependencies, Context.plug, Code.dependencies,
    List.mem_append, or_comm]

theorem context_resource_membership (context : Context) (expression : Code) (resource : Nat) :
    resource ∈ resourceDependencies (context.plug expression).dependencies ↔
      resource ∈ resourceDependencies context.dependencies ∨
      resource ∈ resourceDependencies expression.dependencies := by
  simp only [mem_resourceDependencies]
  exact context_dependency_membership context expression (.resource resource)

theorem expression_access_mono {before after : Code}
    (bound : after.dependencies ⊆ before.dependencies)
    (support : resourceDependencies before.dependencies ⊆ available) :
    resourceDependencies after.dependencies ⊆ available := by
  intro resource retained
  exact support (mem_resourceDependencies.mpr (bound (mem_resourceDependencies.mp retained)))

theorem clause_resource_retained (clause : ClauseAt operation clauses parameter binder body)
    (retained : Dependency.resource resource ∈ body.dependencies) :
    Dependency.resource resource ∈ clauses.dependencies := by
  induction clause with
  | hit =>
      exact List.mem_append_left _ (mem_without.mpr ⟨mem_without.mpr ⟨retained, by simp⟩, by simp⟩)
  | pass different next ih => exact List.mem_append_right _ (ih retained)

theorem selected_handler_access (cut : HandlerCut requested whole cap tail handler)
    (support : Supported whole.erase ambient) :
    handler.erase.access ⊆ tail.erase.visible ++ ambient := by
  induction cut with
  | hit handler tail same => cases support with
      | push frame rest ambient next access => exact access
  | push frame rest cap tail handler miss next ih => cases support with
      | push frame rest ambient next access => exact ih next
  | live ticket q a saved scope rest cap tail handler next ih => cases support with
      | live ticket q a saved rest ambient capture next => exact ih next
  | spent ticket a scope rest cap tail handler next ih => cases support with
      | spent ticket a rest ambient next => exact ih next

theorem raw_step_preserves_access (step : RawStep before after created discharged)
    (valid : AccessValid before ambient) (checked : AccessChecks before ambient) :
    AccessValid after ambient := by
  obtain ⟨control, expression⟩ := valid
  cases step with
  | @focus whole child plain focus tail =>
      have split : ∀ resource,
          resource ∈ resourceDependencies plain.context.dependencies ∨
          resource ∈ resourceDependencies child.dependencies →
          resource ∈ tail.erase.visible ++ ambient := by
        intro resource retained
        apply expression
        rw [← focus_reconstructs focus]
        exact (context_resource_membership _ _ _).mpr retained
      constructor
      · exact .push plain.erase tail.erase ambient control (fun _ retained => split _ (Or.inl retained))
      · intro resource retained
        simpa [Stack.erase, ExecFrame.erase, PlainData.erase, Control.visible, Frame.visible] using
          split resource (Or.inr retained)
  | plug plain value closed scope tail =>
      cases control with
      | push frame rest ambient next contextAccess =>
          constructor
          · exact next
          · intro resource retained
            rcases (context_resource_membership _ _ _).mp retained with fromContext | fromValue
            · exact contextAccess fromContext
            · simpa [Stack.erase, ExecFrame.erase, PlainData.erase, Control.visible, Frame.visible] using
                expression fromValue
  | bind parameter value suffix scope tail closed environmentReady =>
      have full : resourceDependencies value.dependencies ++ resourceDependencies suffix.dependencies ⊆ tail.erase.visible ++ ambient := by
        simpa only [Code.dependencies, resource_dependencies_append, resource_dependencies_without_variable] using expression
      exact ⟨control, substitution_resource_support suffix value parameter
        (fun _ member => full (List.mem_append_right _ member)) (fun _ member => full (List.mem_append_left _ member))⟩
  | beta parameter body value scope tail closed closureReady =>
      have full : resourceDependencies body.dependencies ++ resourceDependencies value.dependencies ⊆ tail.erase.visible ++ ambient := by
        simpa only [Code.dependencies, resource_dependencies_append, resource_dependencies_without_variable] using expression
      exact ⟨control, substitution_resource_support body value parameter
        (fun _ member => full (List.mem_append_left _ member)) (fun _ member => full (List.mem_append_right _ member))⟩
  | ifTrue yes no scope tail =>
      exact ⟨control, expression_access_mono
        (fun _ member => List.mem_append_left _ (List.mem_append_right _ member)) expression⟩
  | ifFalse yes no scope tail =>
      exact ⟨control, expression_access_mono (fun _ member => List.mem_append_right _ member) expression⟩
  | enterHandler handler body tail =>
      have full : handler.effectInst.resources ++ resourceDependencies body.dependencies ++
          resourceDependencies handler.clauses.dependencies ⊆ tail.erase.visible ++ ambient := by
        simpa only [Code.dependencies, resource_dependencies_append, resource_dependencies_map, frozen_effect_atoms] using expression
      constructor
      · apply Supported.push handler.erase tail.erase ambient control
        intro resource retained
        rcases List.mem_append.mp retained with fromInstance | fromClauses
        · exact full (List.mem_append_left _ (List.mem_append_left _ fromInstance))
        · exact full (List.mem_append_right _ fromClauses)
      · intro resource retained
        have inside := full (List.mem_append_left _ (List.mem_append_right _ retained))
        simpa [Stack.erase, ExecFrame.erase, HandlerData.erase, Control.visible, Frame.visible] using inside
  | leaveHandler handler value closed scope tail =>
      cases control with
      | push frame rest ambient next access =>
          exact ⟨next, by simpa [Stack.erase, ExecFrame.erase, HandlerData.erase, Control.visible, Frame.visible] using expression⟩
  | enterCell binder identity payload body scope answer tail instantiationReady =>
      constructor
      · exact .push _ _ _ control (by simp [ExecFrame.erase])
      · intro resource retained
        rcases List.mem_append.mp (acquisition_dependency_bound binder identity body (mem_resourceDependencies.mp retained)) with previous | introduced
        · have earlier := expression (mem_resourceDependencies.mpr previous)
          simpa [Stack.erase, ExecFrame.erase, Control.visible, Frame.visible, List.append_assoc] using
            List.mem_cons_of_mem identity earlier
        · have same : resource = identity := by simpa using introduced
          simp [same, Stack.erase, ExecFrame.erase, Control.visible, Frame.visible]
  | leaveCell identity payload answer savedScope scope value closed tail =>
      cases control with
      | push frame rest ambient next access =>
          constructor
          · exact next
          · intro resource retained
            have previous : resource ∈ identity :: (tail.erase.visible ++ ambient) := by
              simpa [Stack.erase, ExecFrame.erase, Control.visible, Frame.visible, List.append_assoc] using expression retained
            rcases List.mem_cons.mp previous with equal | outside
            · subst resource
              exact False.elim (checked.release _ _ _ _ _ _ _ rfl closed retained)
            · exact outside
  | enterCleanup action body tail =>
      have full : resourceDependencies action.action.dependencies ++ resourceDependencies body.dependencies ⊆
          tail.erase.visible ++ ambient := by
        simpa only [Code.dependencies, resource_dependencies_append] using expression
      constructor
      · exact .push action.erase tail.erase ambient control (fun _ retained => full (List.mem_append_left _ retained))
      · intro resource retained
        simpa [Stack.erase, ExecFrame.erase, ActionData.erase, Control.visible, Frame.visible] using
          full (List.mem_append_right _ retained)
  | startCleanup action saved closed scope tail =>
      have savedAccess : resourceDependencies saved.dependencies ⊆ tail.erase.visible ++ ambient := by
        simpa [Stack.erase, ExecFrame.erase, ActionData.erase, Control.visible, Frame.visible] using expression
      constructor
      · exact start_cleanup_preserves_retained_support control closed savedAccess
      · cases control with
        | push frame rest ambient next actionAccess =>
            simpa [Code.dependencies, resourceDependencies, Stack.erase, ExecFrame.erase,
              ActionData.erase, Control.visible, Frame.visible] using actionAccess
  | finishCleanup action saved closed scope tail =>
      cases control with
      | push frame rest ambient next access =>
          exact ⟨next, fun _ retained => access (List.mem_append_right _ retained)⟩
  | capture requested operation parameter binder ticket operand body scope whole cap tail handler
      operationResult selection clause closed environmentReady =>
      have provider := selected_handler_access selection control
      constructor
      · exact capture_preserves_support (sourceCut_is_cut (handler_cut_erases selection)) control
      · intro resource retained
        have bound := body.subst_dependencies parameter operand (mem_resourceDependencies.mp retained)
        rcases List.mem_append.mp bound with fromBody | fromOperand
        · apply provider
          exact List.mem_append_right _ (mem_resourceDependencies.mpr
            (clause_resource_retained clause fromBody))
        · exact checked.capture _ _ _ _ _ _ _ _ rfl selection closed
            (mem_resourceDependencies.mpr fromOperand)
  | resume binder ticket scope callerScope q a front cap tail value closed resolve =>
      constructor
      · simpa only [erase_append, Stack.erase] using resume_preserves_support
          (by simpa only [erase_append, Stack.erase] using control)
      · intro resource retained
        have previous : resource ∈ (front.erase.visible ++ tail.erase.visible) ++ ambient := by
          have old := expression (by simpa [Code.dependencies, resourceDependencies] using retained)
          simpa [erase_append, Stack.erase, Control.visible] using old
        simpa [erase_append, Stack.erase, Control.visible, List.append_assoc] using
          List.mem_append_right cap.erase.visible previous
  | discard binder ticket closeId scope callerScope q a front cap tail plan resolve build =>
      constructor
      · have supported := discard_control_preserves_support
          (by simpa only [erase_append, Stack.erase] using control)
          (checked.discard _ _ _ _ _ _ _ _ _ _ rfl resolve build)
          (closeId := closeId)
        simpa only [erase_append, Stack.erase, close_control_erases, ExecFrame.erase] using supported
      · simp [Code.dependencies, resourceDependencies]
  | leaveClause ticket answer value closed scope callerScope tail =>
      cases control with
      | spent ticket answer rest ambient next => exact ⟨next, expression⟩
  | finishClose identity scope callerScope tail =>
      cases control with
      | push frame rest ambient next access => exact ⟨next, by simp [Code.dependencies, resourceDependencies]⟩
  | retire ticket scope tail =>
      cases control with
      | push frame rest ambient next access => exact ⟨next, by simp [Code.dependencies, resourceDependencies]⟩
  | readCell identity payload scope before after selected =>
      exact ⟨by simpa only [cell_update_erases selected] using control, by simp [Code.dependencies, resourceDependencies]⟩
  | writeCell identity old new scope before after selected =>
      exact ⟨by simpa only [cell_update_erases selected] using control, by simp [Code.dependencies, resourceDependencies]⟩

/-- An independently defined execution step with local access admission.
    This does not assert that source checking supplies admission. -/
structure AccessRunStep (ambient : List Nat) (before after : RunState) : Prop where
  execution : RunStep before after
  checks : AccessChecks before.configuration ambient

inductive AccessRunSteps (ambient : List Nat) : RunState → RunState → Prop where
  | refl (state : RunState) : AccessRunSteps ambient state state
  | next (first : AccessRunStep ambient before middle)
      (rest : AccessRunSteps ambient middle after) : AccessRunSteps ambient before after

theorem access_run_step_preserves (step : AccessRunStep ambient before after)
    (support : AccessValid before.configuration ambient) :
    AccessValid after.configuration ambient := by
  obtain ⟨execution, checks⟩ := step
  cases execution with
  | event after created discharged raw fresh =>
      exact raw_step_preserves_access raw support checks

theorem access_run_steps_execute (steps : AccessRunSteps ambient before after) :
    RunSteps before after := by
  induction steps with
  | refl state => exact .refl state
  | next first rest ih => exact .next first.execution ih

theorem access_run_steps_preserve (steps : AccessRunSteps ambient before after)
    (support : AccessValid before.configuration ambient) :
    AccessValid after.configuration ambient := by
  induction steps with
  | refl => exact support
  | next first rest ih => exact ih (access_run_step_preserves first support)

theorem access_run_joint_preservation (steps : AccessRunSteps ambient before after)
    (ledger : Ledger before.erase) (support : AccessValid before.configuration ambient) :
    Ledger after.erase ∧ AccessValid after.configuration ambient :=
  ⟨run_steps_preserve_ledger (access_run_steps_execute steps) ledger,
    access_run_steps_preserve steps support⟩

/-- Active access is backed by an owner; owning a dormant capture alone does
    not imply access in the other direction. -/
theorem closed_expression_resource_live
    (support : AccessValid configuration [])
    (retained : resource ∈ resourceDependencies configuration.expression.dependencies) :
    Owner.resource resource ∈ configuration.stack.erase.owners :=
  visible_resource_owned (by simpa using support.expression retained)

/-- For closed, locally admitted executions, a current expression cannot
    retain a completed resource. This is safety, not eventual release. -/
theorem access_run_no_completed_reference (steps : AccessRunSteps [] before after)
    (ledger : Ledger before.erase) (support : AccessValid before.configuration [])
    (retained : resource ∈ resourceDependencies after.configuration.expression.dependencies) :
    Owner.resource resource ∉ after.completed := by
  obtain ⟨finalLedger, finalSupport⟩ := access_run_joint_preservation steps ledger support
  exact ledger_no_live_completed_alias finalLedger
    (closed_expression_resource_live finalSupport retained)

/-- The same exclusion holds for all retained frames, including dormant
    captures and saved cleanup results. -/
theorem access_run_no_completed_retained_reference (steps : AccessRunSteps [] before after)
    (ledger : Ledger before.erase) (support : AccessValid before.configuration [])
    (retained : resource ∈ retainedResources after.configuration.stack.erase) :
    Owner.resource resource ∉ after.completed := by
  obtain ⟨finalLedger, finalSupport⟩ := access_run_joint_preservation steps ledger support
  rcases retained_resource_supported finalSupport.control retained with external | owned
  · simp at external
  · exact ledger_no_live_completed_alias finalLedger owned

structure NamedAccessStep (ambient : List Nat) (before after : NamedState) : Prop where
  execution : NamedStep before after
  checks : AccessChecks before.execution.configuration ambient

inductive NamedAccessSteps (ambient : List Nat) : NamedState → NamedState → Prop where
  | refl (state : NamedState) : NamedAccessSteps ambient state state
  | next (first : NamedAccessStep ambient before middle)
      (rest : NamedAccessSteps ambient middle after) : NamedAccessSteps ambient before after

theorem named_access_steps_have_names (steps : NamedAccessSteps ambient before after) :
    NamedSteps before after := by
  induction steps with
  | refl => exact .refl _
  | next first rest ih => exact .next first.execution ih

theorem named_access_step_preserves (step : NamedAccessStep ambient before after)
    (ledger : Ledger before.execution.erase) (history : NameHistory before.execution before.activations)
    (access : AccessValid before.execution.configuration ambient) :
    Ledger after.execution.erase ∧ NameHistory after.execution after.activations ∧
      AccessValid after.execution.configuration ambient := by
  obtain ⟨nextLedger, nextHistory⟩ := named_step_preserves step.execution ledger history
  exact ⟨nextLedger, nextHistory,
    access_run_step_preserves ⟨named_step_executes step.execution, step.checks⟩ access⟩

theorem named_access_steps_preserve (steps : NamedAccessSteps ambient before after)
    (ledger : Ledger before.execution.erase) (history : NameHistory before.execution before.activations)
    (access : AccessValid before.execution.configuration ambient) :
    Ledger after.execution.erase ∧ NameHistory after.execution after.activations ∧
      AccessValid after.execution.configuration ambient := by
  induction steps with
  | refl => exact ⟨ledger, history, access⟩
  | next first rest ih =>
      obtain ⟨nextLedger, nextHistory, nextAccess⟩ := named_access_step_preserves first ledger history access
      exact ih nextLedger nextHistory nextAccess


theorem resource_free_access_checks {configuration : Configuration}
    (free : resourceDependencies configuration.expression.dependencies = [])
    (notDiscard : ∀ binder, configuration.expression ≠ .discard binder) :
    AccessChecks configuration ambient := by
  constructor
  · intro identity payload answer savedScope scope value tail same closed
    have expr := congrArg Configuration.expression same
    rw [expr] at free
    simp [free]
  · intro requested operation operand scope whole cap tail handler same selected closed
    have expr := congrArg Configuration.expression same
    rw [expr] at free
    have empty : resourceDependencies operand.dependencies = [] := by
      simpa [Code.dependencies] using (List.append_eq_nil_iff.mp
        (by simpa only [Code.dependencies, resource_dependencies_append] using free)).2
    simp [empty]
  · intro binder ticket scope callerScope q answer front cap tail plan same resolve build
    exact False.elim (notDiscard binder (congrArg Configuration.expression same))

/-- An access-annotated raw trace keeps freshness independent, as RawTrace does. -/
inductive AccessTrace (ambient : List Nat) : Configuration → Configuration → List Owner → List Owner → Prop where
  | refl (configuration : Configuration) : AccessTrace ambient configuration configuration [] []
  | next (first : RawStep before middle created discharged)
      (checks : AccessChecks before ambient)
      (rest : AccessTrace ambient middle after laterCreated laterDischarged) :
      AccessTrace ambient before after (created ++ laterCreated) (laterDischarged ++ discharged)

theorem access_trace_enacts (trace : AccessTrace ambient before after created discharged)
    (fresh : (issued ++ created).Nodup) :
    AccessRunSteps ambient ⟨before, issued, completed⟩
      ⟨after, issued ++ created, discharged ++ completed⟩ := by
  induction trace generalizing issued completed with
  | refl configuration =>
      simpa using AccessRunSteps.refl (ambient := ambient) (⟨configuration, issued, completed⟩ : RunState)
  | @next before middle made done after laterMade laterDone first checks rest ih =>
      have allFresh : ((issued ++ made) ++ laterMade).Nodup := by simpa [List.append_assoc] using fresh
      have firstStep : AccessRunStep ambient ⟨before, issued, completed⟩
          ⟨middle, issued ++ made, done ++ completed⟩ :=
        ⟨.event _ _ _ _ first (List.nodup_append.mp allFresh).1, checks⟩
      have following := ih (issued := issued ++ made) (completed := done ++ completed) allFresh
      simpa only [List.append_assoc] using AccessRunSteps.next firstStep following

theorem cell_update_excludes_handler_cut {capture tail : Stack} {selected : HandlerData}
    (update : CellUpdate identity old new before after) :
    ¬ HandlerCut (.cell identity) before capture tail selected := by
  induction update generalizing capture tail selected with
  | hit =>
      intro cut
      cases cut with
      | push frame rest cap tail handler miss next => exact miss rfl
  | push miss next ih =>
      intro cut
      cases cut with
      | hit handler tail same => exact miss (by simp [ExecFrame.erase, HandlerData.erase, Frame.target, same])
      | push frame rest cap tail handler otherMiss further => exact ih further
  | live next ih => intro cut; cases cut with | live _ _ _ _ _ _ _ _ _ further => exact ih further
  | spent next ih => intro cut; cases cut with | spent _ _ _ _ _ _ _ further => exact ih further


theorem freeze_effect_injective : Function.Injective freezeEffect := by
  intro left right same
  have checked := frozen_effect_realizes Environment.empty left
  rw [same] at checked
  exact effect_realization_unique checked (frozen_effect_realizes Environment.empty right)

theorem builtin_request_access_checks (update : CellUpdate identity old new before after) :
    AccessChecks ⟨.perform (freezeEffect (.cell identity)) operation operand, scope, before⟩ ambient := by
  constructor
  · intro resource payload answer savedScope current value tail same closed
    cases same
    exact False.elim closed.1
  · intro requested operation argument current whole cap tail handler same cut closed
    have expression := congrArg Configuration.expression same
    have instanceEq := freeze_effect_injective (Code.perform.inj expression).1
    subst requested
    cases same
    exact False.elim (cell_update_excludes_handler_cut update cut)
  · intro binder owner current caller input answer front cap tail plan same
    cases same

theorem scoped_named_access_preserves_invariants (steps : NamedAccessSteps ambient before after)
    (closed : before.execution.configuration.ResourceClosed) (ledger : Ledger before.execution.erase)
    (history : NameHistory before.execution before.activations) (access : AccessValid before.execution.configuration ambient) :
    after.execution.configuration.ResourceClosed ∧ Ledger after.execution.erase ∧
      NameHistory after.execution after.activations ∧ AccessValid after.execution.configuration ambient :=
  ⟨run_steps_preserve_resource_closure (named_steps_execute (named_access_steps_have_names steps)) closed,
    named_access_steps_preserve steps ledger history access⟩

namespace AccessExamples

def initial : RunState := ⟨⟨.resource 4 (.integer 17) (Examples.readBody 4), .none, .nil⟩, [], []⟩
def terminal : RunState := ⟨⟨.integer 17, .none, .nil⟩, [.resource 0], [.resource 0]⟩

theorem fresh_read_access_trace :
    AccessTrace [] initial.configuration terminal.configuration [.resource 0] [.resource 0] := by
  have entry := RawStep.enterCell 4 0 17 (Examples.readBody 4) .none .integer Stack.nil rfl
  rw [Examples.read_body_instantiates] at entry
  have read := RawStep.readCell 0 17 .none (.push (.cell 0 17 .none .integer) .nil)
    (.push (.cell 0 17 .none .integer) .nil) .hit
  have leave := RawStep.leaveCell 0 17 .integer .none .none (.integer 17)
    ⟨trivial, rfl, by intro _ present; cases present⟩ Stack.nil
  exact .next entry (resource_free_access_checks rfl (by intro _ impossible; cases impossible))
    (.next read (builtin_request_access_checks (new := 17) CellUpdate.hit)
      (.next leave (resource_free_access_checks rfl (by intro _ impossible; cases impossible)) (.refl _)))

theorem fresh_read_admitted_execution : AccessRunSteps [] initial terminal :=
  access_trace_enacts fresh_read_access_trace (issued := []) (completed := []) (by decide)

theorem fresh_read_named_access_execution : NamedAccessSteps [] ⟨initial, []⟩ ⟨terminal, []⟩ := by
  have entry := RawStep.enterCell 4 0 17 (Examples.readBody 4) .none .integer Stack.nil rfl
  rw [Examples.read_body_instantiates] at entry
  have read := RawStep.readCell 0 17 .none (.push (.cell 0 17 .none .integer) .nil)
    (.push (.cell 0 17 .none .integer) .nil) .hit
  have leave := RawStep.leaveCell 0 17 .integer .none .none (.integer 17)
    ⟨trivial, rfl, by intro _ present; cases present⟩ Stack.nil
  exact .next ⟨.event _ _ _ _ entry (by decide) (by decide),
      resource_free_access_checks rfl (by intro _ impossible; cases impossible)⟩
    (.next ⟨.event _ _ _ _ read (by decide) (by decide), builtin_request_access_checks (new := 17) CellUpdate.hit⟩
      (.next ⟨.event _ _ _ _ leave (by decide) (by decide),
        resource_free_access_checks rfl (by intro _ impossible; cases impossible)⟩ (.refl _)))

theorem fresh_read_all_four_invariants :
    terminal.configuration.ResourceClosed ∧ Ledger terminal.erase ∧
      NameHistory terminal [] ∧ AccessValid terminal.configuration [] := by
  apply scoped_named_access_preserves_invariants fresh_read_named_access_execution
  · exact ⟨rfl, trivial⟩
  · exact ⟨.refl _, by decide⟩
  · refine ⟨?_, ?_, by decide⟩ <;> intro name <;> simp [initial, Stack.erase, Control.ticketNames, Control.activations]
  · exact ⟨.nil [], List.nil_subset _⟩

theorem fresh_read_preserves_closure_ownership_and_access :
    terminal.configuration.ResourceClosed ∧ Ledger terminal.erase ∧ AccessValid terminal.configuration [] :=
  ⟨run_steps_preserve_resource_closure (access_run_steps_execute fresh_read_admitted_execution) ⟨rfl, trivial⟩,
    access_run_joint_preservation fresh_read_admitted_execution ⟨.refl _, by decide⟩ ⟨.nil [], List.nil_subset _⟩⟩

/-- Resolving the reference's name does not authorize releasing its owner. -/
theorem name_closure_does_not_allow_dangling_release :
    (Code.resourceRef (.activation 4)).ResourceClosed ∧
    ¬ AccessChecks ⟨.resourceRef (.activation 4), .none, .push (.cell 4 0 .none .unit) .nil⟩ [] := by
  refine ⟨rfl, ?_⟩
  intro checked
  exact checked.release 4 0 .unit .none .none (.resourceRef (.activation 4)) .nil rfl
    ⟨trivial, rfl, by intro dependency present; obtain rfl := List.mem_singleton.mp present; trivial⟩
    (by simp [Code.dependencies, resourceDependencies])

end AccessExamples

end Ash.OneShot.ScopedExecution

#print axioms Ash.OneShot.ScopedExecution.raw_step_preserves_access
#print axioms Ash.OneShot.ScopedExecution.access_run_joint_preservation
#print axioms Ash.OneShot.ScopedExecution.access_run_no_completed_reference
#print axioms Ash.OneShot.ScopedExecution.access_run_no_completed_retained_reference
#print axioms Ash.OneShot.ScopedExecution.named_access_steps_preserve
#print axioms Ash.OneShot.ScopedExecution.scoped_named_access_preserves_invariants
#print axioms Ash.OneShot.ScopedExecution.AccessExamples.fresh_read_preserves_closure_ownership_and_access
#print axioms Ash.OneShot.ScopedExecution.AccessExamples.name_closure_does_not_allow_dangling_release
#print axioms Ash.OneShot.ScopedExecution.AccessExamples.fresh_read_named_access_execution
#print axioms Ash.OneShot.ScopedExecution.AccessExamples.fresh_read_all_four_invariants
