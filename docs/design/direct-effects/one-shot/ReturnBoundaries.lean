import ReturnSupport

/-!
Preserved normal-return obligations for actual active and saved resource
boundaries. Existing obligations survive control movement. A fresh resource
entry supplies its own local bound; deriving that certificate from source
analysis remains separate from this runtime invariant.
-/

namespace Ash.OneShot.ReturnBoundaries
open ResultSummaries ReturnSupport Syntax ScopedExpressions ScopedExecution ScopedPorts

def Excludes (identity : Nat) (summary : Summary) : Prop :=
  ∃ resources, summary.support = some resources ∧ identity ∉ resources

/-- Canonical first-order values and finite inferred storage bounds are
    independent sufficient justifications. Function ports alone are not bounds. -/
def CellBound (identity : Nat) (answer : Ty) (summary : Summary) : Prop :=
  Excludes identity summary ∨
    (eraseType answer).FirstOrder ∧ identity ∉ (eraseType answer).resources

def FrameChecked : ExecFrame → Summary → Prop
  | .cell identity _ _ answer, summary => CellBound identity answer summary
  | _, _ => True

def Checked (environment : ResultSummaries.Environment) : Stack → Summary → Prop
  | .nil, _ => True
  | .push frame tail, summary => FrameChecked frame summary ∧
      Checked environment tail (frameResult environment frame summary)
  | .live _ _ _ saved _ tail, _ => Checked environment saved .unknown ∧ Checked environment tail .unknown
  | .spent _ _ _ tail, _ => Checked environment tail .unknown

def ConfigurationChecked (environment : ResultSummaries.Environment) (configuration : Configuration) : Prop :=
  Checked environment configuration.stack (analyze environment configuration.expression)

theorem excludes_monotone (below : Below actual upper) (excluded : Excludes identity upper) :
    Excludes identity actual := by
  obtain ⟨resources, known, absent⟩ := excluded
  obtain ⟨retained, actualKnown, contained⟩ := below resources known
  exact ⟨retained, actualKnown, fun member => absent (contained member)⟩

theorem cell_bound_monotone (below : Below actual upper) (checked : CellBound identity answer upper) :
    CellBound identity answer actual :=
  checked.elim (fun inferred => Or.inl (excludes_monotone below inferred)) Or.inr

theorem frame_checked_monotone (below : Below actual upper) (checked : FrameChecked frame upper) :
    FrameChecked frame actual := by
  cases frame with
  | cell => exact cell_bound_monotone below checked
  | plain | handler | armed | running | unwinding | closing | retiring => trivial

theorem checked_monotone (stack : Stack) (below : Below actual upper) (checked : Checked environment stack upper) :
    Checked environment stack actual := by
  induction stack generalizing actual upper with
  | nil => trivial
  | push frame tail ih => exact ⟨frame_checked_monotone below checked.1,
      ih (frame_result_monotone frame below) checked.2⟩
  | live | spent => exact checked

theorem checked_append (front tail : Stack) (summary : Summary) :
    Checked environment (front.append tail) summary ↔
      Checked environment front summary ∧ Checked environment tail (stackResult environment front summary) := by
  induction front generalizing summary with
  | nil => simp [Stack.append, Checked, stackResult]
  | push frame rest ih => simp only [Stack.append, Checked, stackResult, ih, and_assoc]
  | live ticket q a saved scope rest ihSaved ihRest =>
      simp only [Stack.append, Checked, stackResult, ihRest, and_assoc]
  | spent ticket a scope rest ih => exact ih _

theorem cut_cap_result (cut : HandlerCut requested whole cap tail handler) :
    stackResult environment cap summary = .unknown := by
    have selected : HandlerCut requested cap cap .nil handler := by
      induction cut with
      | hit handler tail same => exact .hit handler .nil same
      | push frame rest cap tail handler miss next ih => exact .push frame cap cap .nil handler miss ih
      | live ticket q a saved scope rest cap tail handler next ih => exact .live ticket q a saved scope cap cap .nil handler ih
      | spent ticket a scope rest cap tail handler next ih => exact .spent ticket a scope cap cap .nil handler ih
    exact cut_result selected summary

theorem checked_cut (cut : HandlerCut requested whole cap tail handler)
    (checked : Checked environment whole summary) :
    Checked environment cap summary ∧ Checked environment tail .unknown := by
  rw [handler_cut_reconstructs cut] at checked
  obtain ⟨inside, outside⟩ := (checked_append cap tail summary).mp checked
  rw [cut_cap_result cut] at outside
  exact ⟨inside, outside⟩

theorem checked_resume {front capture tail : Stack}
    (checked : Checked environment (front.append (.live owner input answer capture caller tail)) .unknown) :
    Checked environment (capture.append (front.append (.spent owner answer caller tail))) summary := by
  obtain ⟨inside, saved, outside⟩ := (checked_append front _ _).mp checked
  apply (checked_append capture _ _).mpr
  refine ⟨checked_monotone capture (Below.unknown _) saved, ?_⟩
  apply (checked_append front _ _).mpr
  exact ⟨checked_monotone front (Below.unknown _) inside, outside⟩

theorem unit_cell_bound : CellBound identity .unit summary :=
  Or.inr ⟨.unit, by simp [eraseType, Port.resources]⟩

/-- Generated release frames have Unit answers. Their return obligation is
    canonical even after an earlier closing frame forgets result precision. -/
theorem close_control_checked (scope : Scope) (plan : List CloseEntry) (summary : Summary) :
    Checked environment (closeControl scope plan) summary := by
  induction plan generalizing summary with
  | nil => trivial
  | cons entry rest ih =>
      cases entry with
      | release identity payload => exact ⟨unit_cell_bound, ih _⟩
      | invoke action | retire ticket => exact ⟨trivial, ih _⟩

theorem checked_discard {front capture tail : Stack}
    (checked : Checked environment (front.append (.live owner input answer capture caller tail)) .unknown) :
    Checked environment ((closeControl scope plan).append
      (.push (.closing closeId scope) (front.append (.spent owner answer caller tail)))) summary := by
  obtain ⟨inside, _, outside⟩ := (checked_append front _ _).mp checked
  apply (checked_append (closeControl scope plan) _ _).mpr
  refine ⟨close_control_checked _ _ _, trivial, ?_⟩
  exact (checked_append front _ _).mpr ⟨inside, outside⟩

theorem cell_update_checked (update : CellUpdate identity old new before after)
    (checked : Checked environment before summary) : Checked environment after summary := by
  induction update generalizing summary with
  | hit => exact checked
  | push miss next ih => exact ⟨checked.1, ih checked.2⟩
  | live next ih => exact ⟨checked.1, ih checked.2⟩
  | spent next ih => exact ih checked

/-- Only an actually allocated resource needs a new local return certificate.
    This is not the full successor invariant or a witness of another step. -/
inductive AllocationReturn (environment : ResultSummaries.Environment) : List Owner → Configuration → Prop where
  | none (absent : ∀ identity, Owner.resource identity ∉ created) : AllocationReturn environment created configuration
  | cell (bound : CellBound identity answer (analyze environment body)) :
      AllocationReturn environment [.resource identity] ⟨body, scope, .push (.cell identity payload savedScope answer) tail⟩

/-- Existing declared-port checking supplies entry return admission for a
    first-order answer. The source world excludes the newly acquired identity;
    no result summary or assertion about all future states is required. -/
theorem typed_first_order_entry_certificate
    (typed : ScopedPorts.Typed signature world values ticket allowed
      (.resource binder (.integer payload) body) result)
    (fresh : identity ∉ world) (shape : result.FirstOrder)
    (annotation : eraseType answer = result) :
    AllocationReturn environment [.resource identity]
      ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ := by
  apply AllocationReturn.cell
  apply Or.inr
  rw [annotation]
  exact ⟨shape, fun retained => fresh (typed_result_in_world typed retained)⟩

theorem typed_first_order_entry_constructs
    (typed : ScopedPorts.Typed signature world values ticket allowed
      (.resource binder (.integer payload) body) result)
    (fresh : identity ∉ world) (shape : result.FirstOrder)
    (annotation : eraseType answer = result)
    (closed : (Code.resource binder (.integer payload) body).ResourceClosed) :
    RawStep ⟨.resource binder (.integer payload) body, scope, tail⟩
      ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ [.resource identity] [] ∧
    AllocationReturn environment [.resource identity]
      ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ :=
  ⟨.enterCell binder identity payload body scope answer tail closed,
    typed_first_order_entry_certificate typed fresh shape annotation⟩

theorem raw_step_preserves_checked
    (step : RawStep before after created discharged)
    (checked : ConfigurationChecked environment before)
    (allocation : AllocationReturn environment created after) :
    ConfigurationChecked environment after := by
  cases step with
  | @focus whole child plain focus tail =>
      have same := context_result_plug (environment := environment) plain.context child
      rw [focus_reconstructs focus] at same
      refine ⟨trivial, ?_⟩
      change Checked environment tail (contextResult environment plain.context (analyze environment child))
      rw [same]
      exact checked
  | plug plain value closed scope tail =>
      simpa only [ConfigurationChecked, Checked, frameResult, context_result_plug] using checked.2
  | bind parameter value suffix scope tail closed ready =>
      exact checked_monotone tail (Below.of_support_eq
        (ResultSummaries.bind_summary_correspondence parameter suffix closed).storage.support.symm) checked
  | beta parameter body value scope tail closed ready =>
      exact checked_monotone tail (upper := analyze environment (.app (.lambda parameter body) value))
        (Below.unknown _) checked
  | ifTrue yes no scope tail => exact checked_monotone tail (Below.join_left _ _) checked
  | ifFalse yes no scope tail => exact checked_monotone tail (Below.join_right _ _) checked
  | enterHandler | enterCleanup => exact ⟨trivial, checked⟩
  | enterCell binder identity payload body scope answer tail ready =>
      cases allocation with
      | none absent => exact False.elim (absent identity List.mem_cons_self)
      | cell bound => exact ⟨bound, checked⟩
  | leaveHandler handler value closed scope tail => exact checked_monotone tail (Below.unknown _) checked.2
  | leaveCell identity payload answer savedScope scope value closed tail => exact checked_monotone tail (Below.unknown _) checked.2
  | startCleanup => exact ⟨trivial, checked.2⟩
  | finishCleanup action saved closed scope tail => exact checked_monotone tail (Below.unknown _) checked.2
  | capture requested operation parameter binder ticket operand body scope whole cap tail handler
      operationResult selection clause closed ready => exact checked_cut selection checked
  | resume binder ticket scope callerScope q a front cap tail value closed resolve => exact checked_resume checked
  | discard binder ticket closeId scope callerScope q a front cap tail plan resolve build => exact checked_discard checked
  | leaveClause ticket answer value closed scope callerScope tail => exact checked_monotone tail (Below.unknown _) checked
  | finishClose identity scope callerScope tail => exact checked_monotone tail (Below.unknown _) checked.2
  | retire ticket scope tail => exact checked_monotone tail (Below.unknown _) checked.2
  | readCell identity payload scope before after selected =>
      exact checked_monotone after (Below.unknown _) (cell_update_checked selected checked)
  | writeCell identity old new scope before after selected =>
      exact checked_monotone after (Below.unknown _) (cell_update_checked selected checked)

/-- An actual fresh event with its local entry certificate. This relation does
    not inspect the identity of a proposition-valued execution proof. -/
inductive EntryChecked (environment : ResultSummaries.Environment) : RunState → RunState → Prop where
  | event (step : RawStep before.configuration after created discharged)
      (fresh : (before.issued ++ created).Nodup)
      (entry : AllocationReturn environment created after) :
      EntryChecked environment before ⟨after, before.issued ++ created, discharged ++ before.completed⟩

inductive EntriesChecked (environment : ResultSummaries.Environment) : RunState → RunState → Prop where
  | refl (state : RunState) : EntriesChecked environment state state
  | next : EntryChecked environment before middle → EntriesChecked environment middle after →
      EntriesChecked environment before after

theorem entry_checked_executes (entry : EntryChecked environment before after) : RunStep before after := by
  cases entry with
  | event step fresh certificate => exact .event before _ _ _ step fresh

theorem entries_checked_execute (entries : EntriesChecked environment before after) : RunSteps before after := by
  induction entries with
  | refl => exact .refl _
  | next first rest ih => exact .next (entry_checked_executes first) ih

theorem run_step_preserves_checked (entry : EntryChecked environment before after)
    (checked : ConfigurationChecked environment before.configuration) :
    ConfigurationChecked environment after.configuration := by
  cases entry with
  | event step fresh certificate => exact raw_step_preserves_checked step checked certificate

theorem run_steps_preserve_checked (entries : EntriesChecked environment before after)
    (checked : ConfigurationChecked environment before.configuration) :
    ConfigurationChecked environment after.configuration := by
  induction entries with
  | refl => exact checked
  | next first rest ih => exact ih (run_step_preserves_checked first checked)

theorem typed_cell_return_excludes
    (typed : ConfigurationTyped signature tickets world
      ⟨value, scope, .push (.cell identity payload savedScope answer) tail⟩ result)
    (closed : ScopedExpressions.ClosedValue value)
    (checked : ConfigurationChecked environment
      ⟨value, scope, .push (.cell identity payload savedScope answer) tail⟩) :
    identity ∉ resourceDependencies value.dependencies := by
  rcases checked.1 with inferred | ⟨shape, _⟩
  · obtain ⟨resources, known, absent⟩ := inferred
    rw [closed_value_storage_sound closed] at known
    cases known
    exact absent
  · exact typed_first_order_cell_return_excludes_identity typed closed.1 shape

theorem value_access_checks
    (typed : ConfigurationTyped signature tickets world configuration result)
    (value : configuration.expression.IsValue)
    (checked : ConfigurationChecked environment configuration) : AccessChecks configuration ambient := by
  constructor
  · intro identity payload answer savedScope scope returned tail same closed
    rw [same] at typed checked
    exact typed_cell_return_excludes typed closed checked
  · intro requested operation operand scope whole cap tail handler same cut closed
    rw [same] at value
    cases value
  · intro binder owner scope caller input answer front cap tail plan same resolve built
    rw [same] at value
    cases value

theorem value_allocation_return (step : RawStep before after created discharged)
    (value : before.expression.IsValue) : AllocationReturn environment created after := by
  cases step <;> exact .none (by simp_all [Code.IsValue])

theorem run_value_preserves_checked (step : RunStep before after)
    (value : before.configuration.expression.IsValue)
    (checked : ConfigurationChecked environment before.configuration) :
    ConfigurationChecked environment after.configuration := by
  cases step with
  | event after created discharged raw fresh =>
      exact raw_step_preserves_checked raw checked (value_allocation_return raw value)

theorem named_value_preserves_checked (step : NamedAccessStep ambient before after)
    (value : before.execution.configuration.expression.IsValue)
    (checked : ConfigurationChecked environment before.execution.configuration) :
    ConfigurationChecked environment after.execution.configuration :=
  run_value_preserves_checked (named_step_executes step.execution) value checked

theorem checked_value_progress
    (valid : ScopedPortJoint.Valid signature policy registry ambient before result outgoing)
    (value : before.execution.configuration.expression.IsValue)
    (checked : ConfigurationChecked environment before.execution.configuration) :
    before.execution.configuration.stack = .nil ∨ ∃ after,
      NamedAccessStep ambient before after ∧
      ScopedPortJoint.Valid signature policy registry ambient after result outgoing ∧
      ConfigurationChecked environment after.execution.configuration := by
  rcases ScopedPortJoint.checked_value_progress valid value
      (value_access_checks (effect_configuration_has_types valid.effects) value checked) with terminal | ⟨after, step, valid⟩
  · exact Or.inl terminal
  · exact Or.inr ⟨after, step, valid, named_value_preserves_checked step value checked⟩

theorem checked_ready_value_progress
    (ready : ScopedPortPrepared.Ready (withCellSignatures users) policy registry ambient before result outgoing)
    (value : before.execution.configuration.expression.IsValue)
    (checked : ConfigurationChecked environment before.execution.configuration) :
    ScopedPortProgress.Terminal before.execution.configuration ∨ ∃ after,
      NamedAccessStep ambient before after ∧
      ScopedPortPrepared.Ready (withCellSignatures users) policy registry ambient after result outgoing ∧
      ConfigurationChecked environment after.execution.configuration := by
  rcases ScopedPortPrepared.checked_ready_value_progress ready value
      (value_access_checks (effect_configuration_has_types ready.joint.effects) value checked) with terminal | ⟨after, step, ready⟩
  · exact Or.inl terminal
  · exact Or.inr ⟨after, step, ready, named_value_preserves_checked step value checked⟩

namespace Examples

def callbackAnswer : Ty := .function .unit .integer [] []

theorem outer_capture_may_return :
    CellBound 7 callbackAnswer (analyze ReturnSupport.Examples.unknownEnvironment
      (ResultSummaries.Examples.retainingConstant 8)) ∧ ¬ (eraseType callbackAnswer).FirstOrder := by
  constructor
  · exact Or.inl ⟨[8], rfl, by simp⟩
  · intro impossible
    cases impossible

theorem own_capture_cannot_return :
    ¬ CellBound 7 callbackAnswer (analyze ReturnSupport.Examples.unknownEnvironment
      (ResultSummaries.Examples.retainingConstant 7)) := by
  intro alleged
  rcases alleged with ⟨resources, known, excluded⟩ | ⟨shape, _⟩
  · have same : resources = [7] := Option.some.inj known.symm
    subst resources
    exact excluded List.mem_cons_self
  · cases shape

def retainingTemplate : Code := .lambda 0 (.bind 1 (.resourceRef (.bound 4)) (.integer 42))

/-- Bound resource names carry no activation atom until entry. Checking only
    the template would wrongly accept the closure returned after opening. -/
theorem template_bound_does_not_admit_opening :
    Excludes 7 (analyze ReturnSupport.Examples.unknownEnvironment retainingTemplate) ∧
    ¬ CellBound 7 callbackAnswer (analyze ReturnSupport.Examples.unknownEnvironment
      (retainingTemplate.instantiate (Instantiation.Environment.empty.bind 4 7))) := by
  refine ⟨⟨[], rfl, by simp⟩, ?_⟩
  exact own_capture_cannot_return

theorem unit_closing_plan_always_has_return_checks (plan : List CloseEntry) :
    Checked environment (closeControl scope plan) .unknown := close_control_checked scope plan .unknown

theorem empty_stack_is_checked (code : Code) : ConfigurationChecked environment ⟨code, scope, .nil⟩ := trivial

def returnFrame : PlainData :=
  ⟨.bind 3 (ResultSummaries.Examples.retainingConstant 8), .none, .unit, callbackAnswer, [], rfl⟩

def returnHandler : HandlerData := { ScopedSignatureGap.Examples.handler with answer := callbackAnswer }

def savedReturn : Stack := .push (.plain returnFrame)
  (.push (.cell 7 41 .none callbackAnswer) (.push (.handler returnHandler) .nil))

theorem saved_return_checked : Checked ReturnSupport.Examples.unknownEnvironment savedReturn .unknown :=
  ⟨trivial, outer_capture_may_return.1, trivial, trivial⟩

theorem saved_return_cut : HandlerCut ScopedSignatureGap.Examples.send savedReturn savedReturn .nil returnHandler := by
  apply HandlerCut.push (.plain returnFrame) _ _ .nil returnHandler (by decide)
  apply HandlerCut.push (.cell 7 41 .none callbackAnswer) _ _ .nil returnHandler (by decide)
  exact .hit returnHandler .nil rfl

def requesting : Configuration :=
  ⟨.perform (Instantiation.freezeEffect ScopedSignatureGap.Examples.send) 0 .unit, .none, savedReturn⟩

def capturedReturn : Configuration :=
  ⟨.resume 9 .unit, .ticket 9 5, .live 5 .unit callbackAnswer savedReturn .none .nil⟩

def resumedReturn : Configuration :=
  ⟨.unit, .ticket 9 5, savedReturn.append (.spent 5 callbackAnswer .none .nil)⟩

/-- The captured cell returns a function, so its saved obligation uses actual
    result support rather than the first-order alternative. These are raw
    events and return certificates, not complete access/typing admission. -/
theorem capture_resume_preserves_function_return :
    RawStep requesting capturedReturn [.ticket 5] [] ∧
    RawStep capturedReturn resumedReturn [] [.ticket 5] ∧
    ConfigurationChecked ReturnSupport.Examples.unknownEnvironment requesting ∧
    ConfigurationChecked ReturnSupport.Examples.unknownEnvironment capturedReturn ∧
    ConfigurationChecked ReturnSupport.Examples.unknownEnvironment resumedReturn := by
  have capture : RawStep requesting capturedReturn [.ticket 5] [] :=
    .capture ScopedSignatureGap.Examples.send 0 5 9 5 .unit (.resume 9 .unit) .none
      savedReturn savedReturn .nil returnHandler .unit saved_return_cut .hit
      ScopedExecution.Examples.unit_closed (by intro name member; simp [Code.dependencies] at member)
  have resume : RawStep capturedReturn resumedReturn [] [.ticket 5] :=
    .resume 9 5 (.ticket 9 5) .none .unit callbackAnswer .nil savedReturn .nil .unit
      ScopedExecution.Examples.unit_closed rfl
  have first : ConfigurationChecked ReturnSupport.Examples.unknownEnvironment capturedReturn :=
    raw_step_preserves_checked capture saved_return_checked (.none (by simp))
  exact ⟨capture, resume, saved_return_checked, first,
    raw_step_preserves_checked resume first (.none (by simp))⟩

end Examples

end Ash.OneShot.ReturnBoundaries

#print axioms Ash.OneShot.ReturnBoundaries.excludes_monotone
#print axioms Ash.OneShot.ReturnBoundaries.cell_bound_monotone
#print axioms Ash.OneShot.ReturnBoundaries.frame_checked_monotone
#print axioms Ash.OneShot.ReturnBoundaries.checked_monotone
#print axioms Ash.OneShot.ReturnBoundaries.checked_append
#print axioms Ash.OneShot.ReturnBoundaries.cut_cap_result
#print axioms Ash.OneShot.ReturnBoundaries.checked_cut
#print axioms Ash.OneShot.ReturnBoundaries.checked_resume
#print axioms Ash.OneShot.ReturnBoundaries.unit_cell_bound
#print axioms Ash.OneShot.ReturnBoundaries.close_control_checked
#print axioms Ash.OneShot.ReturnBoundaries.checked_discard
#print axioms Ash.OneShot.ReturnBoundaries.cell_update_checked
#print axioms Ash.OneShot.ReturnBoundaries.typed_first_order_entry_certificate
#print axioms Ash.OneShot.ReturnBoundaries.typed_first_order_entry_constructs
#print axioms Ash.OneShot.ReturnBoundaries.raw_step_preserves_checked
#print axioms Ash.OneShot.ReturnBoundaries.entry_checked_executes
#print axioms Ash.OneShot.ReturnBoundaries.entries_checked_execute
#print axioms Ash.OneShot.ReturnBoundaries.run_step_preserves_checked
#print axioms Ash.OneShot.ReturnBoundaries.run_steps_preserve_checked
#print axioms Ash.OneShot.ReturnBoundaries.typed_cell_return_excludes
#print axioms Ash.OneShot.ReturnBoundaries.value_access_checks
#print axioms Ash.OneShot.ReturnBoundaries.value_allocation_return
#print axioms Ash.OneShot.ReturnBoundaries.run_value_preserves_checked
#print axioms Ash.OneShot.ReturnBoundaries.named_value_preserves_checked
#print axioms Ash.OneShot.ReturnBoundaries.checked_value_progress
#print axioms Ash.OneShot.ReturnBoundaries.checked_ready_value_progress
#print axioms Ash.OneShot.ReturnBoundaries.Examples.outer_capture_may_return
#print axioms Ash.OneShot.ReturnBoundaries.Examples.own_capture_cannot_return
#print axioms Ash.OneShot.ReturnBoundaries.Examples.template_bound_does_not_admit_opening
#print axioms Ash.OneShot.ReturnBoundaries.Examples.unit_closing_plan_always_has_return_checks
#print axioms Ash.OneShot.ReturnBoundaries.Examples.empty_stack_is_checked
#print axioms Ash.OneShot.ReturnBoundaries.Examples.saved_return_checked
#print axioms Ash.OneShot.ReturnBoundaries.Examples.saved_return_cut
#print axioms Ash.OneShot.ReturnBoundaries.Examples.capture_resume_preserves_function_return
