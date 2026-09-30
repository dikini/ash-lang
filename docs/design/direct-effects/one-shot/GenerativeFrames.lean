import GenerativeResults

/-!
Saved ordinary environments and structural result-bound transformations for
actual contexts and control forests. This extends the result-support component;
handler clause admission and whole-run progress remain separate obligations.
-/

namespace Ash.OneShot.GenerativeFrames
open Instantiation ScopedExpressions ScopedExecution
open GenerativeResults (Derives summary)
open ResultSummaries (extendAnalysis)
open DeclarationResults (signature)


/-- Rebinding a closed returned value changes analysis metadata, not its
    stored dependencies. It supplies no environment equivalence for open code. -/
theorem closed_value_check (closed : ClosedValue value)
    (included : Syntax.resourceDependencies value.dependencies ⊆ bound) :
    DeclarationTemplates.check declarations environment bound value = true := by
  apply DeclarationTemplates.check_iff_source_bound.mpr
  refine ⟨Syntax.resourceDependencies value.dependencies, ?_, included⟩
  rw [DeclarationTemplates.runtime_agreement value closed.2.1,
    OperationResults.closed_value_storage_sound closed]
  rfl

theorem returned_value_rebind (checked : Derives declarations environment world value bound)
    (closed : ClosedValue value) : Derives declarations savedEnvironment savedWorld value bound :=
  .leaf (Or.inl closed.1) closed.2.1 (closed_value_check closed (GenerativeResults.value_support checked closed))

/-- Context holes correspond exactly to the existing strict evaluation
    contexts. Each frame keeps its caller's support environment. -/
inductive ContextReturns (declarations : DeclarationRegistry) (environment : ResultSummaries.Environment)
    (world : List Nat) : Context → List Nat → List Nat → Prop where
  | pairLeft (rightChecked : Derives declarations environment world right rightBound) :
      ContextReturns declarations environment world (.pairLeft right) leftBound (leftBound ++ rightBound)
  | pairRight (leftChecked : Derives declarations environment world left leftBound) :
      ContextReturns declarations environment world (.pairRight left) rightBound (leftBound ++ rightBound)
  | bind (bodyChecked : Derives declarations (extendAnalysis environment name (summary inputBound)) world body outputBound) :
      ContextReturns declarations environment world (.bind name body) inputBound outputBound
  | branch (yesChecked : Derives declarations environment world yes bound)
      (noChecked : Derives declarations environment world no bound) :
      ContextReturns declarations environment world (.branch yes no) conditionBound bound
  | perform (closed : (Code.perform effect operation .unit).ResourceClosed)
      (checked : DeclarationTemplates.check declarations environment bound (.perform effect operation .unit) = true) :
      ContextReturns declarations environment world (.perform effect operation) operandBound bound
  | resource (closed : (Code.resource binder .unit body).ResourceClosed)
      (bodyChecked : ∀ identity, identity ∉ world → Derives declarations environment (world ++ [identity])
        (body.instantiate (Environment.empty.bind binder identity)) bound)
      (outward : bound ⊆ world) :
      ContextReturns declarations environment world (.resource binder body) initializerBound bound

theorem plug_resource_closed (context : Context)
    (contextClosed : (context.plug .unit).ResourceClosed) (codeClosed : code.ResourceClosed) :
    (context.plug code).ResourceClosed := by
  cases context <;> simp_all [Context.plug, Code.ResourceClosed, Code.freeNames, List.append_eq_nil_iff]
  assumption

theorem context_plug (context : ContextReturns declarations environment world position input output)
    (child : Derives declarations environment world code input) :
    Derives declarations environment world (position.plug code) output := by
  cases context with
  | pairLeft right => exact .pair child right
  | pairRight left => exact .pair left child
  | bind body => exact .bind child body
  | branch yes no => exact .branch child yes no
  | perform closed checked =>
      exact .perform child (plug_resource_closed (.perform _ _) closed (GenerativeResults.resource_closed child)) checked
  | resource closed body outward =>
      exact .resource child (plug_resource_closed (.resource _ _) closed (GenerativeResults.resource_closed child)) body outward

theorem context_plug_returned_value
    (context : ContextReturns declarations savedEnvironment world position input output)
    (child : Derives declarations currentEnvironment currentWorld value input)
    (closed : ClosedValue value) :
    Derives declarations savedEnvironment world (position.plug value) output :=
  context_plug context (returned_value_rebind child closed)

theorem context_world_mono
    (context : ContextReturns declarations environment world position input output)
    (included : world ⊆ larger) : ContextReturns declarations environment larger position input output := by
  cases context with
  | pairLeft right => exact .pairLeft (GenerativeResults.world_mono right included)
  | pairRight left => exact .pairRight (GenerativeResults.world_mono left included)
  | bind body => exact .bind (GenerativeResults.world_mono body included)
  | branch yes no => exact .branch (GenerativeResults.world_mono yes included) (GenerativeResults.world_mono no included)
  | perform closed checked => exact .perform closed checked
  | resource closed body outward =>
      apply ContextReturns.resource closed _ (outward.trans included)
      intro identity fresh
      exact GenerativeResults.world_mono (body identity (fun member => fresh (included member)))
        (ScopedExpressions.append_subset included (List.Subset.refl _))

/-- Every actual focus of a supported computation yields a child derivation
    and its matching context certificate, including an ignored initializer. -/
theorem focus_decompose (checked : Derives declarations environment world whole output)
    (focus : Focus whole child position) :
    ∃ input, Derives declarations environment world child input ∧
      ContextReturns declarations environment world position input output := by
  cases checked with
  | leaf shape closed finite =>
      rcases shape with value | ⟨name, rfl⟩
      · exact False.elim (ScopedTyping.focus_is_not_value focus value)
      · cases focus
  | pair left right => cases focus with
      | pairLeft => exact ⟨_, left, .pairLeft right⟩
      | pairRight => exact ⟨_, right, .pairRight left⟩
  | bind initializer body => cases focus with
      | bind => exact ⟨_, initializer, .bind body⟩
  | branch condition yes no => cases focus with
      | branch => exact ⟨_, condition, .branch yes no⟩
  | perform operand closed finite => cases focus with
      | perform =>
          refine ⟨_, operand, .perform ?_ finite⟩
          simpa only [Code.ResourceClosed, Code.freeNames, List.append_nil] using (List.append_eq_nil_iff.mp closed).1
  | resource initializer closed body outward => cases focus with
      | resource =>
          refine ⟨_, initializer, .resource ?_ body outward⟩
          exact (List.append_eq_nil_iff.mp closed).2

/-- Finite support supplied by the actual saved input port. Callable input
    ports remain unknown at this layer. The answer bound is separate. -/
def ResumeBound (input : Ty) (bound : List Nat) : Prop :=
  ∃ resources, (ContinuationBounds.portBound (ScopedPorts.eraseType input)).support = some resources ∧ resources ⊆ bound

/-- Every plain frame retains its own analysis environment. Saved captures
    keep their own result interface; append extends only the active tail. -/
inductive StackReturns (declarations : DeclarationRegistry) (world : List Nat) :
    Stack → List Nat → List Nat → Prop where
  | nil : StackReturns declarations world .nil bound bound
  | plain (context : ContextReturns declarations environment world plain.context input middle)
      (rest : StackReturns declarations world tail middle output) :
      StackReturns declarations world (.push (.plain plain) tail) input output
  | cell (absent : identity ∉ input) (rest : StackReturns declarations world tail input output) :
      StackReturns declarations world (.push (.cell identity payload scope answer) tail) input output
  | handler (rest : StackReturns declarations world tail input output) :
      StackReturns declarations world (.push (.handler handler) tail) input output
  | live (port : ResumeBound operationInput resumeInput)
      (saved : StackReturns declarations world capture resumeInput savedOutput)
      (rest : StackReturns declarations world tail clauseOutput output) :
      StackReturns declarations world (.live owner operationInput answer capture scope tail) clauseOutput output
  | spent (rest : StackReturns declarations world tail input output) :
      StackReturns declarations world (.spent owner answer scope tail) input output

variable {front capture tail : Stack}

theorem stack_world_mono (checked : StackReturns declarations world stack input output)
    (included : world ⊆ larger) : StackReturns declarations larger stack input output := by
  induction checked with
  | nil => exact .nil
  | plain context rest ih => exact .plain (context_world_mono context included) ih
  | cell absent rest ih => exact .cell absent ih
  | handler rest ih => exact .handler ih
  | live port saved rest ihSaved ihRest => exact .live port ihSaved ihRest
  | spent rest ih => exact .spent ih

theorem stack_append (front : StackReturns declarations world left input middle)
    (tail : StackReturns declarations world right middle output) :
    StackReturns declarations world (left.append right) input output := by
  induction front with
  | nil => exact tail
  | plain context rest ih => exact .plain context (ih tail)
  | cell absent rest ih => exact .cell absent (ih tail)
  | handler rest ih => exact .handler (ih tail)
  | live port saved rest ihSaved ihRest => exact .live port saved (ihRest tail)
  | spent rest ih => exact .spent (ih tail)

theorem stack_decompose {front tail : Stack}
    (checked : StackReturns declarations world (front.append tail) input output) :
    ∃ middle, StackReturns declarations world front input middle ∧
      StackReturns declarations world tail middle output := by
  induction front generalizing input output with
  | nil => exact ⟨input, .nil, checked⟩
  | push frame rest ih => cases checked with
      | plain context next =>
          obtain ⟨middle, inside, outside⟩ := ih next
          exact ⟨middle, .plain context inside, outside⟩
      | cell absent next =>
          obtain ⟨middle, inside, outside⟩ := ih next
          exact ⟨middle, .cell absent inside, outside⟩
      | handler next =>
          obtain ⟨middle, inside, outside⟩ := ih next
          exact ⟨middle, .handler inside, outside⟩
  | live owner operationInput answer saved scope rest ihSaved ihRest => cases checked with
      | live port capture next =>
          obtain ⟨middle, inside, outside⟩ := ihRest next
          exact ⟨middle, .live port capture inside, outside⟩
  | spent owner answer scope rest ih => cases checked with
      | spent next =>
          obtain ⟨middle, inside, outside⟩ := ih next
          exact ⟨middle, .spent inside, outside⟩

theorem cell_spine_embeds (spine : GenerativeResults.CellSpine bound stack) :
    StackReturns declarations world stack bound bound := by
  induction spine with
  | nil => exact .nil
  | cell absent rest ih => exact .cell absent ih

/-- The chosen clause still needs its own result derivation at the exposed
    answer bound. A control certificate does not establish that clause premise. -/
theorem capture_certificate (cut : HandlerCut requested whole capture tail handler)
    (checked : StackReturns declarations world whole inputBound outputBound)
    (port : ResumeBound operationInput inputBound) :
    ∃ answerBound, StackReturns declarations world capture inputBound answerBound ∧
      StackReturns declarations world
        (.live owner operationInput handler.answer capture handler.scope tail) answerBound outputBound := by
  rw [handler_cut_reconstructs cut] at checked
  obtain ⟨answerBound, saved, outside⟩ := stack_decompose checked
  exact ⟨answerBound, saved, .live port saved outside⟩

/-- Resumption requires the saved output B to be the prefix input B. The
    current live boundary alone does not establish this compatibility. -/
theorem resume_recomposition
    (port : ResumeBound operationInput resumeInput)
    (saved : StackReturns declarations world capture resumeInput savedOutput)
    (frontChecked : StackReturns declarations world front savedOutput clauseOutput)
    (outside : StackReturns declarations world tail clauseOutput outputBound) :
    StackReturns declarations world
      (front.append (.live owner operationInput answer capture caller tail)) savedOutput outputBound ∧
    StackReturns declarations world
      (capture.append (front.append (.spent owner answer caller tail))) resumeInput outputBound :=
  ⟨stack_append frontChecked (.live port saved outside), stack_append saved (stack_append frontChecked (.spent outside))⟩

def ConfigurationReturns (declarations : DeclarationRegistry) (world : List Nat)
    (configuration : Configuration) (output : List Nat) : Prop :=
  ∃ environment input, Derives declarations environment world configuration.expression input ∧
    StackReturns declarations world configuration.stack input output

theorem focus_step (focus : Focus whole child plain.context)
    (checked : ConfigurationReturns declarations world ⟨whole, plain.scope, tail⟩ output) :
    RawStep ⟨whole, plain.scope, tail⟩ ⟨child, plain.scope, .push (.plain plain) tail⟩ [] [] ∧
    ConfigurationReturns declarations world ⟨child, plain.scope, .push (.plain plain) tail⟩ output := by
  obtain ⟨environment, bound, code, stack⟩ := checked
  obtain ⟨input, childChecked, context⟩ := focus_decompose code focus
  exact ⟨.focus plain focus tail, environment, input, childChecked, .plain context stack⟩

theorem plug_step
    (checked : ConfigurationReturns declarations world ⟨value, scope, .push (.plain plain) tail⟩ output)
    (closed : ClosedValue value) :
    RawStep ⟨value, scope, .push (.plain plain) tail⟩ ⟨plain.context.plug value, plain.scope, tail⟩ [] [] ∧
    ConfigurationReturns declarations world ⟨plain.context.plug value, plain.scope, tail⟩ output := by
  obtain ⟨environment, input, code, stack⟩ := checked
  cases stack with
  | plain context rest =>
      exact ⟨.plug plain value closed scope tail, _, _, context_plug_returned_value context code closed, rest⟩

theorem bind_step
    (checked : ConfigurationReturns declarations world ⟨.bind name value body, scope, tail⟩ output)
    (closed : ClosedValue value) (suffixClosed : ClosedExcept name body) :
    RawStep ⟨.bind name value body, scope, tail⟩ ⟨body.subst name value, scope, tail⟩ [] [] ∧
    ConfigurationReturns declarations world ⟨body.subst name value, scope, tail⟩ output := by
  obtain ⟨environment, bound, code, stack⟩ := checked
  obtain ⟨input, afterBound⟩ := GenerativeResults.bind_value_derivation code closed
  exact ⟨.bind name value body scope tail closed suffixClosed, _, bound, afterBound, stack⟩

theorem resource_step
    (checked : ConfigurationReturns declarations world ⟨.resource binder (.integer payload) body, scope, tail⟩ output)
    (fresh : identity ∉ world) :
    RawStep ⟨.resource binder (.integer payload) body, scope, tail⟩
      ⟨body.instantiate (Environment.empty.bind binder identity), scope, .push (.cell identity payload scope answer) tail⟩
      [.resource identity] [] ∧
    ConfigurationReturns declarations (world ++ [identity])
      ⟨body.instantiate (Environment.empty.bind binder identity), scope, .push (.cell identity payload scope answer) tail⟩ output := by
  obtain ⟨environment, bound, code, stack⟩ := checked
  obtain ⟨step, bodyChecked, absent⟩ := GenerativeResults.resource_entry code fresh
  exact ⟨step, environment, bound, bodyChecked, .cell absent
    (stack_world_mono stack (List.subset_append_left _ _))⟩

theorem cell_return_step
    (checked : ConfigurationReturns declarations world ⟨value, scope, .push (.cell identity payload savedScope answer) tail⟩ output)
    (closed : ClosedValue value) :
    RawStep ⟨value, scope, .push (.cell identity payload savedScope answer) tail⟩ ⟨value, savedScope, tail⟩ [] [.resource identity] ∧
    AccessChecks ⟨value, scope, .push (.cell identity payload savedScope answer) tail⟩ ambient ∧
    ConfigurationReturns declarations world ⟨value, savedScope, tail⟩ output := by
  obtain ⟨environment, bound, code, stack⟩ := checked
  cases stack with
  | cell absent rest =>
      exact ⟨.leaveCell identity payload answer savedScope scope value closed tail,
        GenerativeResults.value_return_access code closed absent, environment, bound, code, rest⟩

theorem handler_return_step
    (checked : ConfigurationReturns declarations world ⟨value, scope, .push (.handler handler) tail⟩ output)
    (closed : ClosedValue value) :
    RawStep ⟨value, scope, .push (.handler handler) tail⟩ ⟨value, handler.scope, tail⟩ [] [] ∧
    ConfigurationReturns declarations world ⟨value, handler.scope, tail⟩ output := by
  obtain ⟨environment, bound, code, stack⟩ := checked
  cases stack with
  | handler rest => exact ⟨.leaveHandler handler value closed scope tail, environment, bound, code, rest⟩

/-- Historical ticket typing authenticates the actual saved input. Prefix
    compatibility with the saved output is supplied separately below. -/
theorem resumed_value_derivation
    (resolved : scope.resolve binder = some owner)
    (typed : ScopedPorts.ConfigurationTyped (signature declarations) tickets world
      ⟨.resume binder value, scope, front.append (.live owner input answer capture caller tail)⟩ result)
    (isValue : value.IsValue) (port : ResumeBound input inputBound) :
    ClosedValue value ∧ Derives declarations environment world value inputBound := by
  obtain ⟨closed, below⟩ := ContinuationBounds.resume_operand_bound (environment := environment) resolved typed isValue
  obtain ⟨resources, known, included⟩ := port
  obtain ⟨retained, actual, smaller⟩ := below resources known
  rw [ResultSummaries.closed_value_storage_sound closed] at actual
  cases actual
  exact ⟨closed, .leaf (Or.inl closed.1) closed.2.1 (closed_value_check closed (smaller.trans included))⟩

theorem resume_step
    (resolved : scope.resolve binder = some owner)
    (typed : ScopedPorts.ConfigurationTyped (signature declarations) tickets world
      ⟨.resume binder value, scope, front.append (.live owner input answer capture caller tail)⟩ result)
    (isValue : value.IsValue) (port : ResumeBound input inputBound)
    (saved : StackReturns declarations world capture inputBound savedOutput)
    (frontChecked : StackReturns declarations world front savedOutput clauseOutput)
    (outside : StackReturns declarations world tail clauseOutput outputBound) :
    RawStep ⟨.resume binder value, scope, front.append (.live owner input answer capture caller tail)⟩
      ⟨value, scope, capture.append (front.append (.spent owner answer caller tail))⟩ [] [.ticket owner] ∧
    ConfigurationReturns declarations world
      ⟨value, scope, capture.append (front.append (.spent owner answer caller tail))⟩ outputBound := by
  obtain ⟨closed, bounded⟩ := resumed_value_derivation (declarations := declarations) (environment := fun _ => .unknown)
    resolved typed isValue port
  exact ⟨.resume binder owner scope caller input answer front capture tail value closed resolved,
    _, inputBound, bounded, (resume_recomposition port saved frontChecked outside).2⟩

namespace Examples

def declarations : DeclarationRegistry := fun family => if family = 83 then
  some ⟨[], [⟨.unit, .integer⟩]⟩ else none
def environment : ResultSummaries.Environment := fun _ => .unknown
def callback : Code := GenerativeResults.Examples.callback
def inner : Code := GenerativeResults.Examples.inner
def nested : Code := GenerativeResults.Examples.program
def initializer : Code := .bind 3 (.integer 99) nested
def program : Code := .bind 3 initializer (.variable 3)
def answer : Ty := GenerativeResults.Examples.answer
def waiting : PlainData := ⟨.bind 3 (.variable 3), .none, answer, answer, [], rfl⟩
def s0 : Configuration := ⟨program, .none, .nil⟩
def s1 : Configuration := ⟨initializer, .none, .push (.plain waiting) .nil⟩
def s2 : Configuration := ⟨nested, .none, .push (.plain waiting) .nil⟩
def s3 : Configuration := ⟨inner, .none, .push (.cell 8 41 .none answer) (.push (.plain waiting) .nil)⟩
def s4 : Configuration := ⟨callback, .none,
  .push (.cell 9 99 .none answer) (.push (.cell 8 41 .none answer) (.push (.plain waiting) .nil))⟩
def s5 : Configuration := ⟨callback, .none, .push (.cell 8 41 .none answer) (.push (.plain waiting) .nil)⟩
def s6 : Configuration := ⟨callback, .none, .push (.plain waiting) .nil⟩
def s7 : Configuration := ⟨.bind 3 callback (.variable 3), .none, .nil⟩
def s8 : Configuration := ⟨callback, .none, .nil⟩

theorem nested_bound (environment : ResultSummaries.Environment) (world : List Nat) :
    Derives declarations environment world nested [] := by
  refine .resource (initializerBound := []) (.leaf (Or.inl trivial) rfl rfl) rfl ?_ (List.nil_subset _)
  intro outer outerFresh
  refine .resource (initializerBound := []) (.leaf (Or.inl trivial) rfl rfl) rfl ?_ (List.nil_subset _)
  intro inner innerFresh
  exact .leaf (Or.inl trivial) rfl rfl

theorem program_bound : Derives declarations environment [] program [] :=
  .bind (inputBound := []) (.bind (inputBound := []) (.leaf (Or.inl trivial) rfl rfl) (nested_bound _ _))
    (.leaf (Or.inr ⟨3, rfl⟩) rfl rfl)

theorem initial_returns : ConfigurationReturns declarations [] s0 [] :=
  ⟨environment, [], program_bound, .nil⟩

theorem e0 : RawStep s0 s1 [] [] ∧ ConfigurationReturns declarations [] s1 [] :=
  focus_step (plain := waiting) (whole := program) (child := initializer)
    (.bind (by simp [initializer, Code.IsValue])) initial_returns

theorem e1 : RawStep s1 s2 [] [] ∧ ConfigurationReturns declarations [] s2 [] :=
  bind_step e0.2 ⟨trivial, rfl, by intro dependency member; cases member⟩
    (by intro name member; cases member)

theorem e2 : RawStep s2 s3 [.resource 8] [] ∧ ConfigurationReturns declarations [8] s3 [] :=
  resource_step e1.2 (by decide)

theorem e3 : RawStep s3 s4 [.resource 9] [] ∧ ConfigurationReturns declarations [8, 9] s4 [] :=
  resource_step e2.2 (by decide)

theorem e4 : RawStep s4 s5 [] [.resource 9] ∧ AccessChecks s4 [] ∧ ConfigurationReturns declarations [8, 9] s5 [] :=
  cell_return_step e3.2 GenerativeResults.Examples.callback_closed

theorem e5 : RawStep s5 s6 [] [.resource 8] ∧ AccessChecks s5 [] ∧ ConfigurationReturns declarations [8, 9] s6 [] :=
  cell_return_step e4.2.2 GenerativeResults.Examples.callback_closed

theorem e6 : RawStep s6 s7 [] [] ∧ ConfigurationReturns declarations [8, 9] s7 [] :=
  plug_step e5.2.2 GenerativeResults.Examples.callback_closed

theorem e7 : RawStep s7 s8 [] [] ∧ ConfigurationReturns declarations [8, 9] s8 [] :=
  bind_step e6.2 GenerativeResults.Examples.callback_closed
    (by simp [ClosedExcept, Code.dependencies])

theorem ordinary_frame_nested_trace : RawTrace s0 s8 [.resource 8, .resource 9] [.resource 8, .resource 9] :=
  .next e0.1 (.next e1.1 (.next e2.1 (.next e3.1 (.next e4.1 (.next e5.1 (.next e6.1 (.next e7.1 (.refl _))))))))

theorem ordinary_frame_nested_execution :
    RunSteps ⟨s0, [], []⟩ ⟨s8, [.resource 8, .resource 9], [.resource 8, .resource 9]⟩ :=
  raw_trace_enacts ordinary_frame_nested_trace (issued := []) (completed := []) (by decide)

theorem ordinary_frame_nested_ledger :
    Ledger (RunState.erase ⟨s8, [.resource 8, .resource 9], [.resource 8, .resource 9]⟩) :=
  run_steps_preserve_ledger ordinary_frame_nested_execution ⟨.refl _, by decide⟩

theorem distinct_saved_environments : environment 3 = .unknown ∧
    extendAnalysis environment 3 (summary []) 3 = .scalar := ⟨rfl, rfl⟩

/-- The saved frame reconstructs its code using its own environment after
    the child has performed a same-name ordinary bind. -/
theorem restored_waiting_environment :
    Derives declarations environment [8, 9] (waiting.context.plug callback) [] := by
  have context : ContextReturns declarations environment [8, 9] waiting.context [] [] :=
    .bind (.leaf (Or.inr ⟨3, rfl⟩) rfl rfl)
  have child : Derives declarations (extendAnalysis environment 3 (summary [])) [8, 9] callback [] :=
    .leaf (Or.inl trivial) rfl rfl
  exact context_plug_returned_value context child GenerativeResults.Examples.callback_closed

theorem integer_resume_port : ResumeBound .integer [] := ⟨[], rfl, List.nil_subset _⟩

theorem saved_capture_returns : StackReturns declarations [7] ContinuationBounds.Examples.saved [] [] :=
  .plain (environment := environment) (.bind (.leaf (Or.inl trivial) rfl rfl))
    (.cell (by simp) (.handler .nil))

theorem actual_capture_keeps_certificate :
    RawStep ContinuationBounds.Examples.requesting ContinuationBounds.Examples.captured [.ticket 5] [] ∧
    ∃ answerBound, StackReturns declarations [7] ContinuationBounds.Examples.saved [] answerBound ∧
      StackReturns declarations [7] ContinuationBounds.Examples.captured.stack answerBound [] :=
  ⟨ContinuationBounds.Examples.typed_capture_and_resume.1,
    capture_certificate ContinuationBounds.Examples.saved_cut saved_capture_returns integer_resume_port⟩

theorem saved_capture_typed (records : ScopedPorts.TicketSignatures) :
    ScopedPorts.StackTyped (signature declarations) records [7] ContinuationBounds.Examples.saved .integer
      (ScopedPorts.eraseType ContinuationBounds.Examples.answer) := by
  have suffix : ScopedPorts.Typed (signature declarations) [7] (ScopedPorts.TypeEnv.empty.extend 3 .integer) .none []
      (.lambda 0 (.variable 3)) (ScopedPorts.eraseType ContinuationBounds.Examples.answer) :=
    .lambda (.variable rfl (List.nil_subset _)) (List.nil_subset _)
  have clauses : ScopedPorts.ClausesTyped (signature declarations) [7] ScopedPorts.TypeEnv.empty
      ContinuationBounds.Examples.family (ScopedPorts.eraseType ContinuationBounds.Examples.answer) []
      ContinuationBounds.Examples.handler.clauses :=
    .cons rfl (.resume .integer (List.Subset.refl []) (List.nil_subset _)) .nil
  have coverage : ScopedPorts.Covers (signature declarations) ContinuationBounds.Examples.family
      ContinuationBounds.Examples.handler.clauses := by
    intro operation input output known
    cases operation with
    | zero => exact List.mem_cons_self
    | succ operation =>
        simp [signature, DeclarationResults.userSignature, declarations, ContinuationBounds.Examples.family,
          ScopedPorts.withCellSignatures] at known
  exact .push (.plain ScopedPorts.ScopeTyped.none (.bind suffix))
    (.push (.cell ⟨_, ScopedPorts.ScopeTyped.none⟩ (by
      simp [ContinuationBounds.Examples.answer, ReturnBoundaries.Examples.callbackAnswer, ScopedPorts.eraseType, ScopedPorts.Port.resources]))
      (.push (.handler ⟨_, ScopedPorts.ScopeTyped.none⟩ clauses coverage (by decide)) .nil))

theorem declared_capture_state_typed :
    ScopedPorts.ConfigurationTyped (signature declarations) ContinuationBounds.Examples.tickets [7]
      ContinuationBounds.Examples.captured (ScopedPorts.eraseType ContinuationBounds.Examples.answer) := by
  refine ⟨ScopedPorts.eraseType ContinuationBounds.Examples.answer,
    ScopedPorts.AtType.checked (allowed := []) (ScopedPorts.ScopeTyped.bound (residual := []) (closing := []) (by rfl)) ?_,
    ScopedPorts.StackTyped.live (by rfl) ⟨_, ScopedPorts.ScopeTyped.none⟩ (saved_capture_typed _) .nil⟩
  apply ScopedPorts.Typed.resume .integer (List.Subset.refl [])
  simp [ScopedPorts.InWorld, ContinuationBounds.Examples.answer, ReturnBoundaries.Examples.callbackAnswer,
    ScopedPorts.eraseType, ScopedPorts.Port.resources]

theorem actual_resume_restores_certificate :
    RawStep ContinuationBounds.Examples.captured ContinuationBounds.Examples.resumed [] [.ticket 5] ∧
    ConfigurationReturns declarations [7] ContinuationBounds.Examples.resumed [] :=
  resume_step (front := .nil) rfl declared_capture_state_typed trivial integer_resume_port
    saved_capture_returns .nil .nil

def retainOuter : PlainData := ⟨.bind 4 (ResultSummaries.Examples.retainingConstant 8),
  .ticket 9 5, answer, answer, [], rfl⟩
def dropOuter : PlainData := ⟨.bind 6 (.integer 17), .none, answer, .integer, [], rfl⟩
def activePrefix : Stack := .push (.plain retainOuter) .nil
def outside : Stack := .push (.plain dropOuter) (.push (.cell 8 0 .none .integer) .nil)

theorem nonempty_prefix_recomposition :
    StackReturns declarations [7, 8]
      (activePrefix.append (.live 5 .integer answer ContinuationBounds.Examples.saved .none outside)) [] [] ∧
    StackReturns declarations [7, 8]
      (ContinuationBounds.Examples.saved.append (activePrefix.append (.spent 5 answer .none outside))) [] [] := by
  have saved : StackReturns declarations [7, 8] ContinuationBounds.Examples.saved [] [] :=
    stack_world_mono saved_capture_returns (by intro identity member; cases List.mem_singleton.mp member; exact List.mem_cons_self)
  have frontChecked : StackReturns declarations [7, 8] activePrefix [] [8] :=
    .plain (environment := environment) (.bind (.leaf (Or.inl trivial) rfl rfl)) .nil
  have rest : StackReturns declarations [7, 8] outside [8] [] :=
    .plain (environment := environment) (.bind (.leaf (Or.inl trivial) rfl rfl)) (.cell (by simp) .nil)
  exact resume_recomposition integer_resume_port saved frontChecked rest

theorem nested_typed (world : List Nat) (environment : ScopedPorts.TypeEnv) (allowed : List Instance) :
    ScopedPorts.Typed (signature declarations) world environment .none allowed nested
      (ScopedPorts.eraseType answer) := by
  refine .resource (residual := []) .integer ?_ (List.nil_subset _) (List.nil_subset _) (List.nil_subset _)
  intro outer outerFresh
  refine .resource (residual := []) .integer ?_ (List.nil_subset _) (List.nil_subset _) (List.nil_subset _)
  intro inner innerFresh
  exact .lambda .integer (List.nil_subset _)

theorem program_typed : ScopedPorts.Typed (signature declarations) [] ScopedPorts.TypeEnv.empty .none [] program
    (ScopedPorts.eraseType answer) :=
  .bind (.bind .integer (nested_typed _ _ _)) (.variable rfl (List.nil_subset _))

def policy : Syntax.TicketPolicy := fun _ => ActionRequirements.resumeOnly

theorem initial_joint_valid : ScopedPortJoint.Valid (signature declarations) policy (fun _ => none) []
    ⟨⟨s0, [], []⟩, []⟩ (ScopedPorts.eraseType answer) [] :=
  ScopedPortJoint.initial_configuration_valid program_typed
    (.bind (.bind .integer (.resource .integer (.resource .integer (.lambda .integer)))) .variable) rfl

theorem callable_port_does_not_erase_retained_support :
    ScopedPorts.Typed (signature declarations) [8] ScopedPorts.TypeEnv.empty .none []
      (ResultSummaries.Examples.retainingConstant 8) (ScopedPorts.eraseType answer) ∧
    ¬ Derives declarations environment [8] (ResultSummaries.Examples.retainingConstant 8) [] := by
  refine ⟨.lambda (.bind (.reference (by decide)) .integer) (List.nil_subset _), ?_⟩
  intro checked
  have closed : ClosedValue (ResultSummaries.Examples.retainingConstant 8) := by
    simp [ClosedValue, ResultSummaries.Examples.retainingConstant, Code.IsValue, Code.ResourceClosed,
      Code.freeNames, ResourceName.freeNames, Code.dependencies, Syntax.without]
  have included := GenerativeResults.value_support checked closed
  exact List.not_mem_nil (included (a := 8) (by decide))

theorem callable_resume_port_remains_unknown (bound : List Nat) : ¬ ResumeBound answer bound := by
  intro ⟨resources, known, included⟩
  cases known

end Examples

end Ash.OneShot.GenerativeFrames

#print axioms Ash.OneShot.GenerativeFrames.closed_value_check
#print axioms Ash.OneShot.GenerativeFrames.returned_value_rebind
#print axioms Ash.OneShot.GenerativeFrames.plug_resource_closed
#print axioms Ash.OneShot.GenerativeFrames.context_plug
#print axioms Ash.OneShot.GenerativeFrames.context_plug_returned_value
#print axioms Ash.OneShot.GenerativeFrames.context_world_mono
#print axioms Ash.OneShot.GenerativeFrames.focus_decompose
#print axioms Ash.OneShot.GenerativeFrames.stack_world_mono
#print axioms Ash.OneShot.GenerativeFrames.stack_append
#print axioms Ash.OneShot.GenerativeFrames.stack_decompose
#print axioms Ash.OneShot.GenerativeFrames.cell_spine_embeds
#print axioms Ash.OneShot.GenerativeFrames.capture_certificate
#print axioms Ash.OneShot.GenerativeFrames.resume_recomposition
#print axioms Ash.OneShot.GenerativeFrames.focus_step
#print axioms Ash.OneShot.GenerativeFrames.plug_step
#print axioms Ash.OneShot.GenerativeFrames.bind_step
#print axioms Ash.OneShot.GenerativeFrames.resource_step
#print axioms Ash.OneShot.GenerativeFrames.cell_return_step
#print axioms Ash.OneShot.GenerativeFrames.handler_return_step
#print axioms Ash.OneShot.GenerativeFrames.resumed_value_derivation
#print axioms Ash.OneShot.GenerativeFrames.resume_step
#print axioms Ash.OneShot.GenerativeFrames.Examples.nested_bound
#print axioms Ash.OneShot.GenerativeFrames.Examples.program_bound
#print axioms Ash.OneShot.GenerativeFrames.Examples.initial_returns
#print axioms Ash.OneShot.GenerativeFrames.Examples.e0
#print axioms Ash.OneShot.GenerativeFrames.Examples.e1
#print axioms Ash.OneShot.GenerativeFrames.Examples.e2
#print axioms Ash.OneShot.GenerativeFrames.Examples.e3
#print axioms Ash.OneShot.GenerativeFrames.Examples.e4
#print axioms Ash.OneShot.GenerativeFrames.Examples.e5
#print axioms Ash.OneShot.GenerativeFrames.Examples.e6
#print axioms Ash.OneShot.GenerativeFrames.Examples.e7
#print axioms Ash.OneShot.GenerativeFrames.Examples.ordinary_frame_nested_trace
#print axioms Ash.OneShot.GenerativeFrames.Examples.ordinary_frame_nested_execution
#print axioms Ash.OneShot.GenerativeFrames.Examples.ordinary_frame_nested_ledger
#print axioms Ash.OneShot.GenerativeFrames.Examples.distinct_saved_environments
#print axioms Ash.OneShot.GenerativeFrames.Examples.restored_waiting_environment
#print axioms Ash.OneShot.GenerativeFrames.Examples.integer_resume_port
#print axioms Ash.OneShot.GenerativeFrames.Examples.saved_capture_returns
#print axioms Ash.OneShot.GenerativeFrames.Examples.actual_capture_keeps_certificate
#print axioms Ash.OneShot.GenerativeFrames.Examples.saved_capture_typed
#print axioms Ash.OneShot.GenerativeFrames.Examples.declared_capture_state_typed
#print axioms Ash.OneShot.GenerativeFrames.Examples.actual_resume_restores_certificate
#print axioms Ash.OneShot.GenerativeFrames.Examples.nonempty_prefix_recomposition
#print axioms Ash.OneShot.GenerativeFrames.Examples.nested_typed
#print axioms Ash.OneShot.GenerativeFrames.Examples.program_typed
#print axioms Ash.OneShot.GenerativeFrames.Examples.initial_joint_valid
#print axioms Ash.OneShot.GenerativeFrames.Examples.callable_port_does_not_erase_retained_support
#print axioms Ash.OneShot.GenerativeFrames.Examples.callable_resume_port_remains_unknown
