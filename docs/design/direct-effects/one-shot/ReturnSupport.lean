import CaptureViewSubstitution

/-!
Conservative normal-result support through actual machine transitions. Unknown
support is top. This observer does not unfold applications, infer precise
control results, or establish that a strict expression returns normally.
-/

namespace Ash.OneShot.ReturnSupport
open ResultSummaries Syntax ScopedExpressions ScopedExecution

/-- A finite bound is informative; an unknown upper bound imposes no claim.
    This relation observes storage only and is not stable under call unfolding. -/
def Below (actual upper : Summary) : Prop :=
  ∀ resources, upper.support = some resources →
    ∃ retained, actual.support = some retained ∧ retained ⊆ resources

namespace Below

theorem refl (summary : Summary) : Below summary summary :=
  fun resources known => ⟨resources, known, List.Subset.refl _⟩

theorem trans (first : Below actual middle) (second : Below middle upper) : Below actual upper := by
  intro resources known
  obtain ⟨between, middleKnown, outer⟩ := second resources known
  obtain ⟨retained, actualKnown, inner⟩ := first between middleKnown
  exact ⟨retained, actualKnown, inner.trans outer⟩

theorem of_support_eq (same : actual.support = upper.support) : Below actual upper := by
  intro resources known
  exact ⟨resources, same.trans known, List.Subset.refl _⟩

theorem unknown (summary : Summary) : Below summary .unknown := by
  intro resources impossible
  cases impossible

theorem rename (below : Below actual upper) (rename : Nat → Nat) :
    Below (actual.rename rename) (upper.rename rename) := by
  simpa only [Below, support_renaming] using below

theorem combine (left : Below a b) (right : Below c d) :
    Below (.product a c) (.product b d) := by
  intro resources known
  cases first : b.support with
  | none => simp [Summary.support, first] at known
  | some xs =>
      cases second : d.support with
      | none => simp [Summary.support, first, second] at known
      | some ys =>
          have same : xs ++ ys = resources := by simpa [Summary.support, first, second] using known
          obtain ⟨actualLeft, leftKnown, leftBound⟩ := left xs first
          obtain ⟨actualRight, rightKnown, rightBound⟩ := right ys second
          refine ⟨actualLeft ++ actualRight, ?_, ?_⟩
          · simp [Summary.support, leftKnown, rightKnown]
          · rw [← same]
            exact append_subset leftBound rightBound

theorem join (left : Below a b) (right : Below c d) :
    Below (.join a c) (.join b d) := combine left right

theorem join_left (left right : Summary) : Below left (.join left right) := by
  intro resources known
  cases first : left.support with
  | none => simp [Summary.support, first] at known
  | some xs =>
      cases second : right.support with
      | none => simp [Summary.support, first, second] at known
      | some ys =>
          have same : xs ++ ys = resources := by simpa [Summary.support, first, second] using known
          exact ⟨xs, rfl, same ▸ List.subset_append_left _ _⟩

theorem join_right (left right : Summary) : Below right (.join left right) := by
  intro resources known
  cases first : left.support with
  | none => simp [Summary.support, first] at known
  | some xs =>
      cases second : right.support with
      | none => simp [Summary.support, first, second] at known
      | some ys =>
          have same : xs ++ ys = resources := by simpa [Summary.support, first, second] using known
          exact ⟨ys, rfl, same ▸ List.subset_append_right _ _⟩

end Below

theorem captured_monotone (dependencies : List Dependency)
    (environmentBound : ∀ name, Below (first name) (second name)) :
    Below (captured first dependencies) (captured second dependencies) := by
  induction dependencies with
  | nil => exact Below.refl _
  | cons dependency rest ih =>
      apply Below.join _ ih
      cases dependency with
      | resource | ticket => exact Below.refl _
      | «variable» name => exact environmentBound name

/-- Only the current support observer is monotone here. All applications stay
    unknown, including when a replacement supplies a known callable. -/
theorem analyze_monotone {code : Code}
    (environmentBound : ∀ name, Below (first name) (second name)) :
    Below (analyze first code) (analyze second code) := by
  cases code with
  | unit | boolean | integer => exact Below.refl _
  | resourceRef name => cases name <;> exact Below.refl _
  | «variable» name => exact environmentBound name
  | pair left right => exact Below.combine (analyze_monotone environmentBound) (analyze_monotone environmentBound)
  | app => exact Below.unknown _
  | branch condition yes no => exact Below.join (analyze_monotone environmentBound) (analyze_monotone environmentBound)
  | perform | handle | resume | discard | resource | cleanup => exact Below.unknown _
  | lambda parameter body => exact captured_monotone _ environmentBound
  | bind parameter initializer body =>
      apply analyze_monotone (code := body)
        (first := fun name => if name = parameter then analyze first initializer else first name)
        (second := fun name => if name = parameter then analyze second initializer else second name)
      intro name
      split
      · exact analyze_monotone environmentBound
      · exact environmentBound name
termination_by sizeOf code

/-- A plain frame retains the same sequencing analysis as its actual plug. -/
def contextResult (environment : ResultSummaries.Environment) : Context → Summary → Summary
  | .pairLeft right, result => .product result (analyze environment right)
  | .pairRight left, result => .product (analyze environment left) result
  | .appFunction argument, result => .application result (analyze environment argument)
  | .appArgument function, result => .application (analyze environment function) result
  | .bind parameter suffix, result => analyze (extendAnalysis environment parameter result) suffix
  | .branch yes no, _ => .join (analyze environment yes) (analyze environment no)
  | .perform _ _, _ | .resume _, _ | .resource _ _, _ | .cleanup _, _ => .unknown

theorem context_result_plug (context : Context) (code : Code) :
    contextResult environment context (analyze environment code) = analyze environment (context.plug code) := by
  cases context <;> rfl

theorem context_result_monotone (context : Context) (below : Below actual upper) :
    Below (contextResult environment context actual) (contextResult environment context upper) := by
  cases context with
  | pairLeft => exact Below.combine below (Below.refl _)
  | pairRight => exact Below.combine (Below.refl _) below
  | appFunction | appArgument | perform | resume | resource | cleanup => exact Below.unknown _
  | branch => exact Below.refl _
  | bind parameter suffix =>
      apply analyze_monotone
      intro name
      unfold extendAnalysis
      split
      · exact below
      · exact Below.refl _

/-- Control boundaries conservatively forget their normal result. This is an
    observer of the existing stack, not a change to its operational behavior. -/
def frameResult (environment : ResultSummaries.Environment) : ExecFrame → Summary → Summary
  | .plain plain, result => contextResult environment plain.context result
  | .handler _, _ | .cell _ _ _ _, _ | .armed _, _ | .running _ _ _, _ | .unwinding _, _ |
    .closing _ _, _ | .retiring _, _ => .unknown

def stackResult (environment : ResultSummaries.Environment) : Stack → Summary → Summary
  | .nil, result => result
  | .push frame tail, result => stackResult environment tail (frameResult environment frame result)
  | .live _ _ _ _ _ tail, _ | .spent _ _ _ tail, _ => stackResult environment tail .unknown

def configurationResult (environment : ResultSummaries.Environment) (configuration : Configuration) : Summary :=
  stackResult environment configuration.stack (analyze environment configuration.expression)

theorem frame_result_monotone (frame : ExecFrame) (below : Below actual upper) :
    Below (frameResult environment frame actual) (frameResult environment frame upper) := by
  cases frame with
  | plain plain => exact context_result_monotone plain.context below
  | handler | cell | armed | running | unwinding | closing | retiring => exact Below.refl _

theorem stack_result_monotone (stack : Stack) (below : Below actual upper) :
    Below (stackResult environment stack actual) (stackResult environment stack upper) := by
  induction stack generalizing actual upper with
  | nil => exact below
  | push frame tail ih => exact ih (frame_result_monotone frame below)
  | live | spent => exact Below.refl _

theorem stack_result_append (front tail : Stack) (summary : Summary) :
    stackResult environment (front.append tail) summary =
      stackResult environment tail (stackResult environment front summary) := by
  induction front generalizing summary <;> simp_all [Stack.append, stackResult]

theorem cut_result (cut : HandlerCut requested whole cap tail handler) (summary : Summary) :
    stackResult environment whole summary = stackResult environment tail .unknown := by
  induction cut generalizing summary with
  | hit => rfl
  | push frame rest cap tail handler miss next ih => exact ih _
  | live ticket q a saved scope rest cap tail handler next ih => exact ih _
  | spent ticket a scope rest cap tail handler next ih => exact ih _

theorem cell_update_result (update : CellUpdate identity old new before after) (summary : Summary) :
    stackResult environment before summary = stackResult environment after summary := by
  induction update generalizing summary with
  | hit => rfl
  | push miss next ih => exact ih _
  | live next ih => exact ih _
  | spent next ih => exact ih _

/-- Each actual transition refines this conservative observation. The statement
    has no access-admission or successor-validity premise. -/
theorem raw_step_result (step : RawStep before after created discharged) :
    Below (configurationResult environment after) (configurationResult environment before) := by
  cases step with
  | @focus whole child plain focus tail =>
      have same := context_result_plug (environment := environment) plain.context child
      rw [focus_reconstructs focus] at same
      simp only [configurationResult, stackResult, frameResult, same]
      exact Below.refl _
  | plug plain value closed scope tail =>
      simp only [configurationResult, stackResult, frameResult, context_result_plug]
      exact Below.refl _
  | bind parameter value suffix scope tail closed ready =>
      exact stack_result_monotone tail (Below.of_support_eq
        (ResultSummaries.bind_summary_correspondence parameter suffix closed).storage.support.symm)
  | beta parameter body value scope tail closed ready =>
      exact stack_result_monotone tail (Below.unknown _)
  | ifTrue yes no scope tail => exact stack_result_monotone tail (Below.join_left _ _)
  | ifFalse yes no scope tail => exact stack_result_monotone tail (Below.join_right _ _)
  | enterHandler | enterCell | enterCleanup | startCleanup => exact Below.refl _
  | leaveHandler handler value closed scope tail => exact stack_result_monotone tail (Below.unknown _)
  | leaveCell identity payload answer savedScope scope value closed tail => exact stack_result_monotone tail (Below.unknown _)
  | finishCleanup action saved closed scope tail => exact stack_result_monotone tail (Below.unknown _)
  | capture requested operation parameter binder ticket operand body scope whole cap tail handler
      operationResult selection clause closed ready =>
      simp only [configurationResult, stackResult, cut_result selection]
      exact Below.refl _
  | resume binder ticket scope callerScope q a front cap tail value closed resolve =>
      simp only [configurationResult, stack_result_append, stackResult]
      exact Below.refl _
  | discard binder ticket closeId scope callerScope q a front cap tail plan resolve build =>
      simp only [configurationResult, stack_result_append, stackResult, frameResult]
      exact Below.refl _
  | leaveClause ticket answer value closed scope callerScope tail => exact stack_result_monotone tail (Below.unknown _)
  | finishClose identity scope callerScope tail => exact stack_result_monotone tail (Below.unknown _)
  | retire ticket scope tail => exact stack_result_monotone tail (Below.unknown _)
  | readCell identity payload scope before after selected =>
      unfold configurationResult
      rw [cell_update_result selected]
      exact stack_result_monotone after (Below.unknown _)
  | writeCell identity old new scope before after selected =>
      unfold configurationResult
      rw [cell_update_result selected]
      exact stack_result_monotone after (Below.unknown _)

theorem run_step_result (step : RunStep before after) :
    Below (configurationResult environment after.configuration) (configurationResult environment before.configuration) := by
  cases step with
  | event after created discharged step fresh => exact raw_step_result step

theorem run_steps_result (steps : RunSteps before after) :
    Below (configurationResult environment after.configuration) (configurationResult environment before.configuration) := by
  induction steps with
  | refl => exact Below.refl _
  | next first rest ih => exact ih.trans (run_step_result first)

theorem raw_trace_result (trace : RawTrace before after created discharged) :
    Below (configurationResult environment after) (configurationResult environment before) := by
  induction trace with
  | refl => exact Below.refl _
  | next first rest ih => exact ih.trans (raw_step_result first)

/-- Partial correctness for actual finite executions, over the full transition
    grammar. A finite source bound bounds the stored resources of a normally
    returned closed value. No normal termination or liveness is asserted. -/
theorem returned_value_support
    (steps : RunSteps before after)
    (initialStack : before.configuration.stack = .nil)
    (finalStack : after.configuration.stack = .nil)
    (returned : ClosedValue after.configuration.expression)
    (bound : (analyze environment before.configuration.expression).support = some resources) :
    resourceDependencies after.configuration.expression.dependencies ⊆ resources := by
  have approximation := run_steps_result (environment := environment) steps
  simp only [configurationResult, initialStack, finalStack, stackResult] at approximation
  obtain ⟨actual, known, contained⟩ := approximation resources bound
  rw [closed_value_storage_sound returned] at known
  cases known
  exact contained

theorem returned_value_excludes
    (steps : RunSteps before after)
    (initialStack : before.configuration.stack = .nil)
    (finalStack : after.configuration.stack = .nil)
    (returned : ClosedValue after.configuration.expression)
    (bound : (analyze environment before.configuration.expression).support = some resources)
    (excluded : identity ∉ resources) :
    identity ∉ resourceDependencies after.configuration.expression.dependencies :=
  fun retained => excluded (returned_value_support steps initialStack finalStack returned bound retained)

namespace Examples

def unknownEnvironment : ResultSummaries.Environment := fun _ => .unknown

theorem unknown_has_no_finite_bound : ¬ Below .unknown .scalar := by
  intro alleged
  obtain ⟨retained, impossible, _⟩ := alleged [] rfl
  cases impossible

theorem branch_bound_includes_both_results :
    (analyze unknownEnvironment (.branch (.boolean condition)
      (ResultSummaries.Examples.retainingConstant 7) (ResultSummaries.Examples.retainingConstant 8))).support = some [7, 8] := by
  simp [analyze, ResultSummaries.Examples.retainingConstant, captured, Code.dependencies, without, Summary.support]

theorem retaining_constant_closed (identity : Nat) :
    ClosedValue (ResultSummaries.Examples.retainingConstant identity) := by
  simp [ScopedExpressions.ClosedValue, ResultSummaries.Examples.retainingConstant, Code.IsValue, Code.ResourceClosed,
    Code.freeNames, Instantiation.ResourceName.freeNames, Code.dependencies, without]

theorem actual_branch_return :
    ∃ before after : RunState,
      RunSteps before after ∧ before.configuration.stack = .nil ∧ after.configuration.stack = .nil ∧
      ClosedValue after.configuration.expression ∧
      (analyze unknownEnvironment before.configuration.expression).support = some [7, 8] ∧
      resourceDependencies after.configuration.expression.dependencies = [7] ∧
      resourceDependencies after.configuration.expression.dependencies ⊆ [7, 8] := by
  let source : Code := .branch (.boolean true)
    (ResultSummaries.Examples.retainingConstant 7) (ResultSummaries.Examples.retainingConstant 8)
  let before : RunState := ⟨⟨source, .none, .nil⟩, [], []⟩
  let after : RunState := ⟨⟨ResultSummaries.Examples.retainingConstant 7, .none, .nil⟩, [], []⟩
  have step : RunStep before after := .event before after.configuration [] []
    (.ifTrue _ _ .none .nil) (by simp [before])
  have run : RunSteps before after := .next step (.refl _)
  have bound : (analyze unknownEnvironment before.configuration.expression).support = some [7, 8] :=
    branch_bound_includes_both_results
  exact ⟨before, after, run, rfl, rfl, retaining_constant_closed 7, bound, rfl,
    returned_value_support run rfl rfl (retaining_constant_closed 7) bound⟩

/-- The initializer is still executed. Its unknown application result can be
    ignored by the suffix's result analysis without claiming it terminates. -/
def ignoredCall : Code :=
  .bind 3 (.app (ResultSummaries.Examples.retainingConstant 7) .unit) (.integer 42)

def ignoredFrame : PlainData :=
  ⟨.bind 3 (.integer 42), .none, .integer, .integer, [], rfl⟩

theorem ignored_call_trace :
    RawTrace ⟨ignoredCall, .none, .nil⟩ ⟨.integer 42, .none, .nil⟩ [] [] := by
  have focus : RawStep ⟨ignoredCall, .none, .nil⟩
      ⟨.app (ResultSummaries.Examples.retainingConstant 7) .unit, .none, .push (.plain ignoredFrame) .nil⟩ [] [] :=
    RawStep.focus ignoredFrame (Focus.bind (by simp [Code.IsValue])) .nil
  have middle := ResultSummaries.Examples.retaining_constant_beta_bind
    (identity := 7) (scope := .none) (tail := .push (.plain ignoredFrame) .nil)
  have closed : ScopedExpressions.ClosedValue (.integer 42) := by
    simp [ScopedExpressions.ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames, Code.dependencies]
  have plug := RawStep.plug ignoredFrame (.integer 42) closed .none .nil
  have finish := RawStep.bind 3 (.integer 42) (.integer 42) .none .nil closed
    (by intro name member; simp [Code.dependencies] at member)
  exact .next focus (.next middle.1 (.next middle.2 (.next plug (.next finish (.refl _)))))

theorem ignored_call_return_support :
    (analyze unknownEnvironment ignoredCall).support = some [] ∧
    ∃ before after : RunState,
      before.configuration = ⟨ignoredCall, .none, .nil⟩ ∧
      after.configuration = ⟨.integer 42, .none, .nil⟩ ∧
      RunSteps before after ∧ resourceDependencies after.configuration.expression.dependencies ⊆ [] := by
  have run := raw_trace_enacts (issued := []) (completed := []) ignored_call_trace (by simp)
  exact ⟨rfl, _, _, rfl, rfl, run, returned_value_support (environment := unknownEnvironment) run rfl rfl
    (by simp [ScopedExpressions.ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames, Code.dependencies]) rfl⟩

theorem known_application_stays_unknown :
    (analyze unknownEnvironment (.app (ResultSummaries.Examples.retainingConstant 7) .unit)).support = none := rfl

/-- The order just proved is deliberately unsuitable for precise unfolding. -/
theorem storage_order_does_not_justify_unfolding :
    Below (ObservationGap.pending 7) (ObservationGap.pending 8) ∧
    ¬ Below (ResultSummaries.callResult (ObservationGap.target 7) .scalar)
      (ResultSummaries.callResult (ObservationGap.target 8) .scalar) := by
  refine ⟨Below.unknown _, ?_⟩
  intro alleged
  obtain ⟨retained, same, contained⟩ := alleged [8] rfl
  have actual : retained = [7] := Option.some.inj same.symm
  subst retained
  have impossible := contained (by simp : 7 ∈ ([7] : List Nat))
  simp at impossible

end Examples

end Ash.OneShot.ReturnSupport

#print axioms Ash.OneShot.ReturnSupport.Below.refl
#print axioms Ash.OneShot.ReturnSupport.Below.trans
#print axioms Ash.OneShot.ReturnSupport.Below.of_support_eq
#print axioms Ash.OneShot.ReturnSupport.Below.unknown
#print axioms Ash.OneShot.ReturnSupport.Below.rename
#print axioms Ash.OneShot.ReturnSupport.Below.combine
#print axioms Ash.OneShot.ReturnSupport.Below.join
#print axioms Ash.OneShot.ReturnSupport.Below.join_left
#print axioms Ash.OneShot.ReturnSupport.Below.join_right
#print axioms Ash.OneShot.ReturnSupport.captured_monotone
#print axioms Ash.OneShot.ReturnSupport.analyze_monotone
#print axioms Ash.OneShot.ReturnSupport.context_result_plug
#print axioms Ash.OneShot.ReturnSupport.context_result_monotone
#print axioms Ash.OneShot.ReturnSupport.frame_result_monotone
#print axioms Ash.OneShot.ReturnSupport.stack_result_monotone
#print axioms Ash.OneShot.ReturnSupport.stack_result_append
#print axioms Ash.OneShot.ReturnSupport.cut_result
#print axioms Ash.OneShot.ReturnSupport.cell_update_result
#print axioms Ash.OneShot.ReturnSupport.raw_step_result
#print axioms Ash.OneShot.ReturnSupport.run_step_result
#print axioms Ash.OneShot.ReturnSupport.run_steps_result
#print axioms Ash.OneShot.ReturnSupport.raw_trace_result
#print axioms Ash.OneShot.ReturnSupport.returned_value_support
#print axioms Ash.OneShot.ReturnSupport.returned_value_excludes
#print axioms Ash.OneShot.ReturnSupport.Examples.unknown_has_no_finite_bound
#print axioms Ash.OneShot.ReturnSupport.Examples.branch_bound_includes_both_results
#print axioms Ash.OneShot.ReturnSupport.Examples.retaining_constant_closed
#print axioms Ash.OneShot.ReturnSupport.Examples.actual_branch_return
#print axioms Ash.OneShot.ReturnSupport.Examples.ignored_call_trace
#print axioms Ash.OneShot.ReturnSupport.Examples.ignored_call_return_support
#print axioms Ash.OneShot.ReturnSupport.Examples.known_application_stays_unknown
#print axioms Ash.OneShot.ReturnSupport.Examples.storage_order_does_not_justify_unfolding
