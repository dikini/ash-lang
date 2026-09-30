import Execution

/-!
Current-expression and retained-control resource support.

This layer proves preservation for raw expression steps satisfying explicit
local access checks. Those checks inspect the pre-step value, capture, and
closing derivation; they do not assume the post-step invariant. Deriving them
for every reachable step from source typing remains a separate obligation.
Ordinary result types, usage protocols, handler availability, and progress are
not established by resource support alone.
-/

namespace Ash.OneShot.Execution
open Syntax

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
    before = ⟨.perform requested operation operand, scope, whole⟩ →
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

@[simp] theorem instance_resource_dependencies (effectInst : Instance) :
    resourceDependencies (instanceDependencies effectInst) = effectInst.resources := by
  simp [resourceDependencies, instanceDependencies, Function.comp_def]

theorem context_dependency_membership (context : Context) (expression : Expr) (dependency : Dependency) :
    dependency ∈ (context.plug expression).dependencies ↔
      dependency ∈ context.dependencies ∨ dependency ∈ expression.dependencies := by
  cases context <;> simp [Context.dependencies, Context.plug, Expr.dependencies,
    List.mem_append, or_comm]

theorem context_resource_membership (context : Context) (expression : Expr) (resource : Nat) :
    resource ∈ resourceDependencies (context.plug expression).dependencies ↔
      resource ∈ resourceDependencies context.dependencies ∨
      resource ∈ resourceDependencies expression.dependencies := by
  simp only [mem_resourceDependencies]
  exact context_dependency_membership context expression (.resource resource)

theorem expression_access_mono {before after : Expr}
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
  | bind parameter value suffix scope tail closed environmentReady fresh =>
      exact ⟨control, expression_access_mono
        (local_step_dependencies (.bind parameter value suffix closed environmentReady fresh)) expression⟩
  | beta parameter body value scope tail closed closureReady fresh =>
      exact ⟨control, expression_access_mono
        (local_step_dependencies (.beta parameter body value closed closureReady fresh)) expression⟩
  | ifTrue yes no scope tail =>
      exact ⟨control, expression_access_mono (local_step_dependencies (.ifTrue yes no)) expression⟩
  | ifFalse yes no scope tail =>
      exact ⟨control, expression_access_mono (local_step_dependencies (.ifFalse yes no)) expression⟩
  | enterHandler handler body tail =>
      have full : handler.effectInst.resources ++ resourceDependencies body.dependencies ++
          resourceDependencies handler.clauses.dependencies ⊆ tail.erase.visible ++ ambient := by
        simpa only [Expr.dependencies, resource_dependencies_append, instance_resource_dependencies] using expression
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
  | enterCell identity payload body scope answer tail =>
      constructor
      · exact .push _ _ _ control (by simp [ExecFrame.erase])
      · intro resource retained
        by_cases same : resource = identity
        · simp [same, Stack.erase, ExecFrame.erase, Control.visible, Frame.visible]
        · have previous : resource ∈ tail.erase.visible ++ ambient := by
            apply expression
            apply mem_resourceDependencies.mpr
            exact mem_without.mpr ⟨mem_resourceDependencies.mp retained, by simpa using same⟩
          simpa [Stack.erase, ExecFrame.erase, Control.visible, Frame.visible, List.append_assoc] using
            List.mem_cons_of_mem identity previous
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
        simpa only [Expr.dependencies, resource_dependencies_append] using expression
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
            simpa [Expr.dependencies, resourceDependencies, Stack.erase, ExecFrame.erase,
              ActionData.erase, Control.visible, Frame.visible] using actionAccess
  | finishCleanup action saved closed scope tail =>
      cases control with
      | push frame rest ambient next access =>
          exact ⟨next, fun _ retained => access (List.mem_append_right _ retained)⟩
  | capture requested operation parameter binder ticket operand body scope whole cap tail handler
      operationResult selection clause closed environmentReady fresh =>
      have provider := selected_handler_access selection control
      constructor
      · exact capture_preserves_support (sourceCut_is_cut (handler_cut_erases selection)) control
      · intro resource retained
        have bound := substitution_bound_for_closed_value body parameter closed (mem_resourceDependencies.mp retained)
        rcases List.mem_append.mp bound with fromBody | fromOperand
        · apply provider
          exact List.mem_append_right _ (mem_resourceDependencies.mpr
            (clause_resource_retained clause (mem_without.mp fromBody).1))
        · exact checked.capture _ _ _ _ _ _ _ _ rfl selection closed
            (mem_resourceDependencies.mpr fromOperand)
  | resume binder ticket scope callerScope q a front cap tail value closed resolve =>
      constructor
      · simpa only [erase_append, Stack.erase] using resume_preserves_support
          (by simpa only [erase_append, Stack.erase] using control)
      · intro resource retained
        have previous : resource ∈ (front.erase.visible ++ tail.erase.visible) ++ ambient := by
          have old := expression (by simpa [Expr.dependencies, resourceDependencies] using retained)
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
      · simp [Expr.dependencies, resourceDependencies]
  | leaveClause ticket answer value closed scope callerScope tail =>
      cases control with
      | spent ticket answer rest ambient next => exact ⟨next, expression⟩
  | finishClose identity scope callerScope tail =>
      cases control with
      | push frame rest ambient next access => exact ⟨next, by simp [Expr.dependencies, resourceDependencies]⟩
  | retire ticket scope tail =>
      cases control with
      | push frame rest ambient next access => exact ⟨next, by simp [Expr.dependencies, resourceDependencies]⟩
  | readCell identity payload scope before after selected =>
      exact ⟨by simpa only [cell_update_erases selected] using control, by simp [Expr.dependencies, resourceDependencies]⟩
  | writeCell identity old new scope before after selected =>
      exact ⟨by simpa only [cell_update_erases selected] using control, by simp [Expr.dependencies, resourceDependencies]⟩

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
theorem visible_resource_owned {control : Control}
    (visible : resource ∈ control.visible) : Owner.resource resource ∈ control.owners := by
  induction control with
  | nil => simp [Control.visible] at visible
  | push frame rest ih =>
      rcases List.mem_append.mp visible with here | outside
      · apply List.mem_append_left
        cases kind : frame.kind <;> simp_all [Frame.visible, Frame.owners]
      · exact List.mem_append_right _ (ih outside)
  | live ticket q a saved rest ihSaved ihRest =>
      exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihRest visible))
  | spent ticket a rest ih => exact ih visible

/-- All retained frame access, including recursively dormant captures. This
    projection records dependencies, not which resources are currently visible. -/
def retainedResources : Control → List Nat
  | .nil => []
  | .push frame rest => frame.access ++ retainedResources rest
  | .live _ _ _ saved rest => retainedResources saved ++ retainedResources rest
  | .spent _ _ rest => retainedResources rest

theorem retained_resource_supported {control : Control} (support : Supported control ambient)
    (retained : resource ∈ retainedResources control) :
    resource ∈ ambient ∨ Owner.resource resource ∈ control.owners := by
  induction support with
  | nil => simp [retainedResources] at retained
  | push frame rest ambient next access ih =>
      rcases List.mem_append.mp retained with here | later
      · rcases List.mem_append.mp (access here) with active | external
        · exact Or.inr (List.mem_append_right _ (visible_resource_owned active))
        · exact Or.inl external
      · rcases ih later with external | owned
        · exact Or.inl external
        · exact Or.inr (List.mem_append_right _ owned)
  | live ticket q a saved rest ambient capture next ihSaved ihRest =>
      rcases List.mem_append.mp retained with dormant | active
      · rcases ihSaved dormant with outside | owned
        · rcases List.mem_append.mp outside with enclosing | external
          · exact Or.inr (List.mem_cons_of_mem _
              (List.mem_append_right _ (visible_resource_owned enclosing)))
          · exact Or.inl external
        · exact Or.inr (List.mem_cons_of_mem _ (List.mem_append_left _ owned))
      · rcases ihRest active with external | owned
        · exact Or.inl external
        · exact Or.inr (List.mem_cons_of_mem _ (List.mem_append_right _ owned))
  | spent ticket a rest ambient next ih => exact ih retained

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

/-- Resource-free expressions need no release or payload support. Discard
    still needs its independent structural close derivation. -/
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
      simpa [Expr.dependencies] using (List.append_eq_nil_iff.mp
        (by simpa only [Expr.dependencies, resource_dependencies_append] using free)).2
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

namespace Examples

/-- The earlier dangling-reference raw transition is rejected before release. -/
theorem dangling_reference_release_rejected :
    ¬ AccessChecks ⟨.resourceRef 4, .none, .push (.cell 4 0 .none .unit) .nil⟩ [] := by
  intro checked
  exact checked.release 4 0 .unit .none .none (.resourceRef 4) .nil rfl
    (closed_reference 4) (by simp [Expr.dependencies, resourceDependencies])

/-- No locally admitted run can reach the raw counterexample's final state. -/
theorem dangling_reference_result_unreachable
    (steps : AccessRunSteps [] before after)
    (support : AccessValid before.configuration [])
    (result : after.configuration = ⟨.resourceRef 4, .none, .nil⟩) : False := by
  have finalSupport := access_run_steps_preserve steps support
  rw [result] at finalSupport
  have unavailable := finalSupport.expression (a := 4)
    (by simp [Expr.dependencies, resourceDependencies])
  simp [Stack.erase, Control.visible] at unavailable

theorem cleanup_outward_capture_access_trace :
    AccessTrace []
      ⟨.handle (.user 1 []) (.cleanup callback (.integer 42)) clauses, .none, .nil⟩
      ⟨.integer 42, .none, .nil⟩
      [.cleanup 7, .ticket 3] [.cleanup 7, .ticket 3] := by
  have select : HandlerCut (.user 1 []) captureStack captureStack .nil handler :=
    .push _ _ _ _ _ (by simp [ExecFrame.erase, Frame.target]) (.hit handler .nil rfl)
  have e0 := RawStep.enterHandler handler (.cleanup callback (.integer 42)) .nil
  have e1 := RawStep.enterCleanup action (.integer 42) handlerStack
  have e2 := RawStep.startCleanup action (.integer 42) (closed_integer 42) .none handlerStack
  have e3 := RawStep.beta 0 callbackBody .unit .none captureStack closed_unit callback_closed
    (by simp [ResourceFresh, Expr.dependencies])
  have e4 := RawStep.capture (.user 1 []) 0 1 9 3 .unit (.resume 9 .unit) .none
    captureStack captureStack .nil handler .unit select (.hit) closed_unit
    (by simp [ClosedExcept, Expr.dependencies]) (by simp [ResourceFresh, Expr.dependencies])
  have e5 := RawStep.resume 9 3 (.ticket 9 3) .none .unit .integer .nil captureStack .nil .unit closed_unit rfl
  have e6 := RawStep.finishCleanup action (.integer 42) (closed_integer 42) (.ticket 9 3)
    (.push (.handler handler) spentStack)
  have e7 := RawStep.leaveHandler handler (.integer 42) (closed_integer 42) .none spentStack
  have e8 := RawStep.leaveClause 3 .integer (.integer 42) (closed_integer 42) .none .none .nil
  refine .next e0 ?_ (.next e1 ?_ (.next e2 ?_ (.next e3 ?_ (.next e4 ?_
    (.next e5 ?_ (.next e6 ?_ (.next e7 ?_ (.next e8 ?_ (.refl _)))))))))
  · exact resource_free_access_checks rfl (by intro binder same; cases same)
  · exact resource_free_access_checks rfl (by intro binder same; cases same)
  · exact resource_free_access_checks rfl (by intro binder same; cases same)
  · exact resource_free_access_checks rfl (by intro binder same; cases same)
  · exact resource_free_access_checks rfl (by intro binder same; cases same)
  · exact resource_free_access_checks rfl (by intro binder same; cases same)
  · exact resource_free_access_checks rfl (by intro binder same; cases same)
  · exact resource_free_access_checks rfl (by intro binder same; cases same)
  · exact resource_free_access_checks rfl (by intro binder same; cases same)

theorem cleanup_outward_capture_joint_execution :
    AccessRunSteps []
      ⟨⟨.handle (.user 1 []) (.cleanup callback (.integer 42)) clauses, .none, .nil⟩, [], []⟩
      ⟨⟨.integer 42, .none, .nil⟩, [.cleanup 7, .ticket 3], [.cleanup 7, .ticket 3]⟩ :=
  access_trace_enacts cleanup_outward_capture_access_trace (by decide)

/-- Returning an outer reference may release an unrelated inner resource. -/
theorem outer_reference_release_checks :
    AccessChecks ⟨.resourceRef 5, .none,
      .push (.cell 4 0 .none .unit) (.push (.cell 5 0 .none .unit) .nil)⟩ [] := by
  constructor
  · intro identity payload answer savedScope scope value tail same closed
    simp only [Configuration.mk.injEq, Stack.push.injEq, ExecFrame.cell.injEq] at same
    rcases same with ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
    simp [Expr.dependencies, resourceDependencies]
  · intro requested operation operand scope whole cap tail handler same
    cases same
  · intro binder ticket scope callerScope q answer front cap tail plan same
    cases same

theorem outer_reference_survives_inner_release :
    AccessRunSteps []
      ⟨⟨.resourceRef 5, .none, .push (.cell 4 0 .none .unit)
        (.push (.cell 5 0 .none .unit) .nil)⟩, [.resource 4, .resource 5], []⟩
      ⟨⟨.resourceRef 5, .none, .push (.cell 5 0 .none .unit) .nil⟩,
        [.resource 4, .resource 5], [.resource 4]⟩ :=
  .next ⟨.event _ _ [] [.resource 4]
    (.leaveCell 4 0 .unit .none .none (.resourceRef 5) (closed_reference 5)
      (.push (.cell 5 0 .none .unit) .nil)) (by decide), outer_reference_release_checks⟩ (.refl _)

theorem outer_reference_joint_invariant :
    Ledger (⟨⟨.resourceRef 5, .none, .push (.cell 5 0 .none .unit) .nil⟩,
      [.resource 4, .resource 5], [.resource 4]⟩ : RunState).erase ∧
    AccessValid ⟨.resourceRef 5, .none, .push (.cell 5 0 .none .unit) .nil⟩ [] := by
  apply access_run_joint_preservation outer_reference_survives_inner_release
  · exact ⟨.refl _, by decide⟩
  · constructor
    · exact .push _ _ _ (.push _ _ _ (.nil []) (by simp [ExecFrame.erase]))
        (by simp [ExecFrame.erase])
    · simp [Expr.dependencies, resourceDependencies, Stack.erase, ExecFrame.erase,
        Control.visible, Frame.visible]

theorem scope_releases_unit_access_trace :
    AccessTrace [] ⟨.resource 4 (.integer 0) .unit, .none, .nil⟩
      ⟨.unit, .none, .nil⟩ [.resource 4] [.resource 4] := by
  refine .next (.enterCell 4 0 .unit .none .unit .nil) ?_
    (.next (.leaveCell 4 0 .unit .none .none .unit closed_unit .nil) ?_ (.refl _))
  · apply resource_free_access_checks <;> simp [Expr.dependencies, resourceDependencies, without]
  · apply resource_free_access_checks <;> simp [Expr.dependencies, resourceDependencies]

theorem scope_releases_unit_joint_execution :
    AccessRunSteps [] ⟨⟨.resource 4 (.integer 0) .unit, .none, .nil⟩, [], []⟩
      ⟨⟨.unit, .none, .nil⟩, [.resource 4], [.resource 4]⟩ :=
  access_trace_enacts scope_releases_unit_access_trace (by decide)

end Examples

end Ash.OneShot.Execution

#print axioms Ash.OneShot.Execution.raw_step_preserves_access

#print axioms Ash.OneShot.Execution.access_run_joint_preservation
#print axioms Ash.OneShot.Execution.access_run_no_completed_reference
#print axioms Ash.OneShot.Execution.Examples.dangling_reference_release_rejected
#print axioms Ash.OneShot.Execution.Examples.dangling_reference_result_unreachable

#print axioms Ash.OneShot.Execution.Examples.cleanup_outward_capture_joint_execution

#print axioms Ash.OneShot.Execution.Examples.outer_reference_joint_invariant
#print axioms Ash.OneShot.Execution.Examples.scope_releases_unit_joint_execution

#print axioms Ash.OneShot.Execution.access_run_no_completed_retained_reference
