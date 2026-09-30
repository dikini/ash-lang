import Access

/-!
Expression types, effect bounds, retained closure resources, and context ports
for the monomorphic administrative fragment. These judgments are independent
of continuation usage and reachable-cut admission. They do not constitute a
complete source checker or a machine progress theorem. Ticket types carry
separate resume and disposal effect contracts. Admission of actual captures
must still validate those contracts, including every invoked close action.
-/

namespace Ash.OneShot.Typing
open Syntax Execution

abbrev TypeEnv := Nat → Option Ty
abbrev Signature := Instance → Nat → Option (Ty × Ty)

def TypeEnv.empty : TypeEnv := fun _ => none

def TypeEnv.extend (environment : TypeEnv) (name : Nat) (type : Ty) : TypeEnv :=
  fun other => if other = name then some type else environment other

/-- Resource support carried by lexical values is included in closure evidence. -/
def retainedSupport (environment : TypeEnv) (dependencies : List Dependency) : List Nat :=
  dependencies.flatMap fun dependency => match dependency with
    | .resource identity => [identity]
    | .variable name => (environment name).toList.flatMap Ty.resources
    | .ticket _ => []

inductive TicketType where
  | none
  | bound : Nat → Ty → Ty → List Instance → List Instance → TicketType
  deriving DecidableEq, Repr

def clauseKeys : Clauses → List Nat
  | .nil => []
  | .cons operation _ _ _ rest => operation :: clauseKeys rest

def Covers (signature : Signature) (effectInst : Instance) (clauses : Clauses) : Prop :=
  ∀ operation operand result, signature effectInst operation = some (operand, result) →
    operation ∈ clauseKeys clauses

mutual
/-- `allowed` bounds immediate effects. Function types separately bound latent
    effects. Lists express membership bounds, not a chosen Core row encoding. -/
inductive Typed (signature : Signature) : TypeEnv → TicketType → List Instance → Expr → Ty → Prop where
  | unit : Typed signature environment ticket allowed .unit .unit
  | boolean : Typed signature environment ticket allowed (.boolean value) .boolean
  | integer : Typed signature environment ticket allowed (.integer value) .integer
  | variable : environment name = some type →
      Typed signature environment ticket allowed (.variable name) type
  | reference : Typed signature environment ticket allowed (.resourceRef identity) (.reference identity)
  | pair : Typed signature environment ticket allowed left leftType →
      Typed signature environment ticket allowed right rightType →
      Typed signature environment ticket allowed (.pair left right) (.product leftType rightType)
  | lambda : Typed signature (environment.extend parameter input) .none latent body output →
      retainedSupport environment (without (.variable parameter) body.dependencies) ⊆ retained →
      Typed signature environment ticket allowed (.lambda parameter body) (.function input output latent retained)
  | app : Typed signature environment ticket allowed function (.function input output latent retained) →
      Typed signature environment ticket allowed argument input → latent ⊆ allowed →
      Typed signature environment ticket allowed (.app function argument) output
  | bind : Typed signature environment ticket allowed initializer input →
      Typed signature (environment.extend parameter input) ticket allowed suffix output →
      Typed signature environment ticket allowed (.bind parameter initializer suffix) output
  | branch : Typed signature environment ticket allowed condition .boolean →
      Typed signature environment ticket allowed yes type → Typed signature environment ticket allowed no type →
      Typed signature environment ticket allowed (.branch condition yes no) type
  | perform : signature effectInst operation = some (input, output) → effectInst ∈ allowed →
      Typed signature environment ticket allowed operand input →
      Typed signature environment ticket allowed (.perform effectInst operation operand) output
  | handle : Typed signature environment ticket (effectInst :: residual) body answer →
      ClausesTyped signature environment effectInst answer residual clauses → Covers signature effectInst clauses →
      (clauseKeys clauses).Nodup → residual ⊆ allowed →
      Typed signature environment ticket allowed (.handle effectInst body clauses) answer
  | resume : Typed signature environment (.bound binder input answer residual closing) allowed operand input →
      residual ⊆ allowed →
      Typed signature environment (.bound binder input answer residual closing) allowed (.resume binder operand) answer
  | discard : closing ⊆ allowed →
      Typed signature environment (.bound binder input answer residual closing) allowed (.discard binder) .unit
  | resource : Typed signature environment ticket allowed initializer .integer →
      Typed signature environment ticket (.cell identity :: residual) body answer →
      identity ∉ answer.resources → identity ∉ residual.flatMap Instance.resources → residual ⊆ allowed →
      Typed signature environment ticket allowed (.resource identity initializer body) answer
  | cleanup : Typed signature environment ticket allowed action (.function .unit .unit latent retained) →
      Typed signature environment ticket allowed body answer → latent ⊆ allowed →
      Typed signature environment ticket allowed (.cleanup action body) answer

inductive ClausesTyped (signature : Signature) : TypeEnv → Instance → Ty → List Instance → Clauses → Prop where
  | nil : ClausesTyped signature environment effectInst answer residual .nil
  | cons : signature effectInst operation = some (input, output) →
      Typed signature (environment.extend parameter input) (.bound binder output answer residual residual) residual body answer →
      ClausesTyped signature environment effectInst answer residual rest →
      ClausesTyped signature environment effectInst answer residual (.cons operation parameter binder body rest)
end

theorem explicit_resource_in_support
    (retained : Dependency.resource identity ∈ dependencies) :
    identity ∈ retainedSupport environment dependencies := by
  exact List.mem_flatMap.mpr ⟨.resource identity, retained, by simp⟩

/-- Value support follows from checked syntax, including closure annotations;
    a plain arrow without retained support would not establish this bound. -/
theorem typed_value_support (typed : Typed signature environment ticket allowed value type)
    (isValue : value.IsValue) : resourceDependencies value.dependencies ⊆ type.resources := by
  cases typed with
  | unit | boolean | integer => simp [Expr.dependencies, resourceDependencies, Ty.resources]
  | «variable» => cases isValue
  | reference => simp [Expr.dependencies, resourceDependencies, Ty.resources]
  | pair left right =>
      intro identity retained
      rcases List.mem_append.mp (by simpa only [Expr.dependencies, resource_dependencies_append] using retained) with l | r
      · exact List.mem_append_left _ (typed_value_support left isValue.1 l)
      · exact List.mem_append_right _ (typed_value_support right isValue.2 r)
  | lambda body captured =>
      intro identity retained
      exact List.mem_append_right _ (captured (explicit_resource_in_support (mem_resourceDependencies.mp retained)))
  | app | bind | branch | perform | handle | resume | discard | resource | cleanup => cases isValue
termination_by sizeOf value

/-- Resource-return admission is derived from value typing and a scoped result
    type, instead of being assumed as a post-state support invariant. -/
theorem typed_return_excludes_resource
    (typed : Typed signature environment ticket allowed value type)
    (closed : ClosedValue value) (doesNotEscape : identity ∉ type.resources) :
    identity ∉ resourceDependencies value.dependencies :=
  fun retained => doesNotEscape (typed_value_support typed closed.1 retained)

/-- A restricted sufficient signature condition: resource annotations in
    operands/results are bounded by the exact instance. General callable
    payloads need not satisfy this condition; use boundary support instead. -/
def SignatureSupported (signature : Signature) : Prop :=
  ∀ effectInst operation input output, signature effectInst operation = some (input, output) →
    input.resources ++ output.resources ⊆ effectInst.resources

/-- A general payload check uses the value's annotated support at the actual
    boundary; it does not require resources to occur in the effect identity. -/
theorem typed_payload_at_boundary {tail : Stack}
    (typed : Typed signature environment ticket allowed operand input)
    (closed : ClosedValue operand)
    (boundary : input.resources ⊆ tail.erase.visible ++ ambient) :
    resourceDependencies operand.dependencies ⊆ tail.erase.visible ++ ambient :=
  fun _ retained => boundary (typed_value_support typed closed.1 retained)

/-- A selected handler's instance support justifies a well-typed closed payload
    outside its captured segment. Signature support is an explicit premise. -/
theorem typed_payload_crosses_cut
    (typed : Typed signature environment ticket allowed operand input)
    (closed : ClosedValue operand)
    (operationType : signature requested operation = some (input, output))
    (signatureSupport : SignatureSupported signature)
    (cut : HandlerCut requested whole cap tail handler)
    (support : Supported whole.erase ambient) :
    resourceDependencies operand.dependencies ⊆ tail.erase.visible ++ ambient := by
  have provider := selected_handler_access cut support
  have selected : handler.effectInst = requested := by
    clear provider support
    induction cut with
    | hit handler tail same => exact same
    | push frame rest cap tail handler miss next ih => exact ih
    | live ticket q a saved scope rest cap tail handler next ih => exact ih
    | spent ticket a scope rest cap tail handler next ih => exact ih
  intro identity retained
  apply provider
  apply List.mem_append_left
  rw [selected]
  exact signatureSupport _ _ _ _ operationType
    (List.mem_append_left _ (typed_value_support typed closed.1 retained))

/-- A context derives input/output ports from its retained syntax. -/
inductive ContextTyped (signature : Signature) : TypeEnv → TicketType → List Instance → Context → Ty → Ty → Prop where
  | pairLeft : Typed signature environment ticket allowed right rightType →
      ContextTyped signature environment ticket allowed (.pairLeft right) leftType (.product leftType rightType)
  | pairRight : Typed signature environment ticket allowed left leftType →
      ContextTyped signature environment ticket allowed (.pairRight left) rightType (.product leftType rightType)
  | appFunction : Typed signature environment ticket allowed argument input → latent ⊆ allowed →
      ContextTyped signature environment ticket allowed (.appFunction argument) (.function input output latent retained) output
  | appArgument : Typed signature environment ticket allowed function (.function input output latent retained) → latent ⊆ allowed →
      ContextTyped signature environment ticket allowed (.appArgument function) input output
  | bind : Typed signature (environment.extend parameter input) ticket allowed suffix output →
      ContextTyped signature environment ticket allowed (.bind parameter suffix) input output
  | branch : Typed signature environment ticket allowed yes type → Typed signature environment ticket allowed no type →
      ContextTyped signature environment ticket allowed (.branch yes no) .boolean type
  | perform : signature effectInst operation = some (input, output) → effectInst ∈ allowed →
      ContextTyped signature environment ticket allowed (.perform effectInst operation) input output
  | resume : residual ⊆ allowed →
      ContextTyped signature environment (.bound binder input answer residual closing) allowed (.resume binder) input answer
  | resource : Typed signature environment ticket (.cell identity :: residual) body answer →
      identity ∉ answer.resources → identity ∉ residual.flatMap Instance.resources → residual ⊆ allowed →
      ContextTyped signature environment ticket allowed (.resource identity body) .integer answer
  | cleanup : Typed signature environment ticket allowed body answer → latent ⊆ allowed →
      ContextTyped signature environment ticket allowed (.cleanup body) (.function .unit .unit latent retained) answer

theorem context_plug_typed (context : ContextTyped signature environment ticket allowed frame input output)
    (child : Typed signature environment ticket allowed expression input) :
    Typed signature environment ticket allowed (frame.plug expression) output := by
  cases context with
  | pairLeft right => exact .pair child right
  | pairRight left => exact .pair left child
  | appFunction argument effects => exact .app child argument effects
  | appArgument function effects => exact .app function child effects
  | bind suffix => exact .bind child suffix
  | branch yes no => exact .branch child yes no
  | perform operation available => exact .perform operation available child
  | resume effects => exact .resume child effects
  | resource body noEscape noEffectEscape effects => exact .resource child body noEscape noEffectEscape effects
  | cleanup body effects => exact .cleanup child body effects

theorem typed_focus_decomposition (focus : Focus whole child context)
    (typed : Typed signature environment ticket allowed whole output) :
    ∃ input, Typed signature environment ticket allowed child input ∧
      ContextTyped signature environment ticket allowed context input output := by
  cases focus with
  | pairLeft notValue => cases typed with
      | pair left right => exact ⟨_, left, .pairLeft right⟩
  | pairRight isValue notValue => cases typed with
      | pair left right => exact ⟨_, right, .pairRight left⟩
  | appFunction notValue => cases typed with
      | app function argument effects => exact ⟨_, function, .appFunction argument effects⟩
  | appArgument isValue notValue => cases typed with
      | app function argument effects => exact ⟨_, argument, .appArgument function effects⟩
  | bind notValue => cases typed with
      | bind initializer suffix => exact ⟨_, initializer, .bind suffix⟩
  | branch notValue => cases typed with
      | branch condition yes no => exact ⟨_, condition, .branch yes no⟩
  | perform notValue => cases typed with
      | perform operation available operand => exact ⟨_, operand, .perform operation available⟩
  | resume notValue => cases typed with
      | resume operand effects => exact ⟨_, operand, .resume effects⟩
  | resource notValue => cases typed with
      | resource initializer body noEscape noEffectEscape effects => exact ⟨_, initializer, .resource body noEscape noEffectEscape effects⟩
  | cleanup notValue => cases typed with
      | cleanup action body effects => exact ⟨_, action, .cleanup body effects⟩

/-- Given lexical ticket translation, focus can construct its actual frame
    with ports derived from the expression, preserving the typed outer stack. -/
theorem focus_constructs_typed_frame
    (typed : Typed signature environment ticket allowed whole output)
    (focus : Focus whole child context)
    (translated : scope.translate context.dependencies = some pending)
    (tailFits : Fits tail.erase output answer) :
    ∃ plain : PlainData,
      plain.context = context ∧ plain.scope = scope ∧
      Typed signature environment ticket allowed child plain.input ∧
      ContextTyped signature environment ticket allowed context plain.input plain.output ∧
      RawStep ⟨whole, scope, tail⟩ ⟨child, scope, .push (.plain plain) tail⟩ [] [] ∧
      Fits (Stack.push (.plain plain) tail).erase plain.input answer := by
  obtain ⟨input, childTyped, contextTyped⟩ := typed_focus_decomposition focus typed
  let plain : PlainData := ⟨context, scope, input, output, pending, translated⟩
  exact ⟨plain, rfl, rfl, childTyped, contextTyped, .focus plain focus tail,
    .push plain.erase tail.erase answer tailFits⟩

/-- Builtin operation typing is tied to this machine's fixed read/write keys.
    Only user signatures are supplied by declarations. -/
def withCellSignatures (users : Signature) : Signature
  | .cell identity, 0 => some (.reference identity, .integer)
  | .cell identity, 1 => some (.product (.reference identity) .integer, .unit)
  | .cell _, _ => none
  | effectInst@(.user _ _), operation => users effectInst operation

theorem cell_signatures_supported (users : Signature)
    (supported : ∀ key arguments operation input output,
      users (.user key arguments) operation = some (input, output) →
      input.resources ++ output.resources ⊆ (Instance.user key arguments).resources) :
    SignatureSupported (withCellSignatures users) := by
  intro effectInst operation input output found
  cases effectInst with
  | user key arguments => exact supported _ _ _ _ _ found
  | cell identity =>
      cases operation with
      | zero =>
          cases found
          simp [Ty.resources, Instance.resources]
      | succ operation => cases operation with
          | zero =>
              cases found
              simp [Ty.resources, Instance.resources]
          | succ operation => cases found

theorem typed_unit_value (typed : Typed signature environment ticket allowed value .unit)
    (isValue : value.IsValue) : value = .unit := by
  cases typed <;> simp_all [Expr.IsValue]

theorem typed_integer_value (typed : Typed signature environment ticket allowed value .integer)
    (isValue : value.IsValue) : ∃ number, value = .integer number := by
  cases typed <;> simp_all [Expr.IsValue]

theorem typed_boolean_value (typed : Typed signature environment ticket allowed value .boolean)
    (isValue : value.IsValue) : ∃ boolean, value = .boolean boolean := by
  cases typed <;> simp_all [Expr.IsValue]

theorem typed_reference_value (typed : Typed signature environment ticket allowed value (.reference identity))
    (isValue : value.IsValue) : value = .resourceRef identity := by
  cases typed <;> simp_all [Expr.IsValue]

theorem typed_function_value
    (typed : Typed signature environment ticket allowed value (.function input output latent retained))
    (isValue : value.IsValue) : ∃ parameter body, value = .lambda parameter body := by
  cases typed <;> simp_all [Expr.IsValue]

theorem clause_at_of_key {clauses : Clauses} (member : operation ∈ clauseKeys clauses) :
    ∃ parameter binder body, ClauseAt operation clauses parameter binder body := by
  cases clauses with
  | nil => simp [clauseKeys] at member
  | cons other parameter binder body rest =>
      by_cases same : operation = other
      · subst other
        exact ⟨parameter, binder, body, .hit⟩
      · have inRest : operation ∈ clauseKeys rest := (List.mem_cons.mp member).resolve_left same
        obtain ⟨p, k, e, next⟩ := clause_at_of_key inRest
        exact ⟨p, k, e, .pass same next⟩
termination_by sizeOf clauses

theorem covered_operation_selects_clause
    (covered : Covers signature effectInst clauses)
    (known : signature effectInst operation = some (input, output)) :
    ∃ parameter binder body, ClauseAt operation clauses parameter binder body :=
  clause_at_of_key (covered _ _ _ known)

theorem selected_clause_typed
    (selected : ClauseAt operation clauses parameter binder body)
    (typed : ClausesTyped signature environment effectInst answer residual clauses) :
    ∃ input output, signature effectInst operation = some (input, output) ∧
      Typed signature (environment.extend parameter input)
        (.bound binder output answer residual residual) residual body answer := by
  induction selected with
  | hit => cases typed with
      | cons signature body rest => exact ⟨_, _, signature, body⟩
  | pass different next ih => cases typed with
      | cons signature body rest => exact ih rest

/-- Immediate effect bounds and the enclosing ticket can change for a value;
    its function body's independently checked contracts remain unchanged. -/
theorem typed_value_transport (typed : Typed signature environment ticket allowed value type)
    (isValue : value.IsValue) (destination : TicketType) (effects : List Instance) :
    Typed signature environment destination effects value type := by
  cases typed with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | «variable» => cases isValue
  | reference => exact .reference
  | pair left right =>
      exact .pair (typed_value_transport left isValue.1 destination effects)
        (typed_value_transport right isValue.2 destination effects)
  | lambda body retained => exact .lambda body retained
  | app | bind | branch | perform | handle | resume | discard | resource | cleanup => cases isValue
termination_by sizeOf value

/-- Only resource frames in the remaining materialized plan interpret a
    request. A resource already released earlier in the plan is unavailable. -/
def planProvides : List CloseEntry → List Instance
  | [] => []
  | .release identity _ :: rest => .cell identity :: planProvides rest
  | .invoke _ :: rest | .retire _ :: rest => planProvides rest

inductive InvocationAt (action : ActionData) : List CloseEntry → List CloseEntry → Prop where
  | here : InvocationAt action (.invoke action :: suffix) suffix
  | later : InvocationAt action rest suffix → InvocationAt action (entry :: rest) suffix

/-- The close contract bounds outward requests. An invocation may additionally
    use a builtin provided by its actual remaining materialized suffix. -/
inductive PlanTyped (signature : Signature) (closing : List Instance) : List CloseEntry → Prop where
  | nil : PlanTyped signature closing []
  | release : PlanTyped signature closing rest → PlanTyped signature closing (.release identity payload :: rest)
  | retire : PlanTyped signature closing rest → PlanTyped signature closing (.retire ticket :: rest)
  | invoke (typed : Typed signature TypeEnv.empty .none [] action.action
      (.function .unit .unit action.requests retained))
      (effects : action.requests ⊆ planProvides tail ++ closing) (rest : PlanTyped signature closing tail) :
      PlanTyped signature closing (.invoke action :: tail)

theorem plan_invocation_contract (position : InvocationAt action plan suffix)
    (typed : PlanTyped signature closing plan) :
    ∃ retained, Typed signature TypeEnv.empty .none [] action.action
      (.function .unit .unit action.requests retained) ∧ action.requests ⊆ planProvides suffix ++ closing := by
  induction position with
  | here => cases typed with
      | invoke typed effects rest => exact ⟨_, typed, effects⟩
  | later next ih => cases typed with
      | release rest | retire rest | invoke _ _ rest => exact ih rest

/-- Each invocation is typed in its local interpretation context. Its request
    bound may be larger than the whole close plan's outward row. -/
theorem disposal_invocation_typed (typed : PlanTyped signature closing plan)
    (position : InvocationAt action plan suffix) :
    Typed signature TypeEnv.empty .none (planProvides suffix ++ closing) (.app action.action .unit) .unit := by
  obtain ⟨retained, callable, effects⟩ := plan_invocation_contract position typed
  exact .app (typed_value_transport callable action.closed.1 .none _) .unit effects

/-- Every effect discharged by planProvides resolves to the corresponding
    actual builtin even when arbitrary surviving outer control is appended. -/
theorem plan_provided_resolves {plan : List CloseEntry}
    (provided : effectInst ∈ planProvides plan) (scope : Scope) (outer : Control) :
    ∃ identity, effectInst = .cell identity ∧
      ((closeControl scope plan).erase.append outer).resolve effectInst = some (.builtin identity) := by
  induction plan with
  | nil => simp [planProvides] at provided
  | cons entry rest ih => cases entry with
      | release identity payload =>
          rcases List.mem_cons.mp provided with same | later
          · subst effectInst
            exact ⟨identity, rfl, by simp [closeControl, CloseEntry.frame, Stack.erase, ExecFrame.erase,
              Control.append, Control.resolve, Frame.resolve]⟩
          · obtain ⟨target, rfl, resolves⟩ := ih later
            refine ⟨target, rfl, ?_⟩
            by_cases same : target = identity
            · subst target
              simp [closeControl, CloseEntry.frame, Stack.erase, ExecFrame.erase,
                Control.append, Control.resolve, Frame.resolve]
            · simpa [closeControl, CloseEntry.frame, Stack.erase, ExecFrame.erase,
                Control.append, Control.resolve, Frame.resolve, same] using resolves
      | invoke action =>
          obtain ⟨target, rfl, resolves⟩ := ih provided
          exact ⟨target, rfl, by simpa [closeControl, CloseEntry.frame, Stack.erase, ExecFrame.erase,
            ActionData.erase, Control.append, Control.resolve, Frame.resolve] using resolves⟩
      | retire ticket =>
          obtain ⟨target, rfl, resolves⟩ := ih provided
          exact ⟨target, rfl, by simpa [closeControl, CloseEntry.frame, Stack.erase, ExecFrame.erase,
            CloseItem.frame, Control.append, Control.resolve, Frame.resolve] using resolves⟩

theorem plan_request_is_outward_or_interpreted
    (typed : PlanTyped signature closing plan) (position : InvocationAt action plan suffix)
    (request : effectInst ∈ action.requests) (scope : Scope) (outer : Control) :
    effectInst ∈ closing ∨ ∃ identity, effectInst = .cell identity ∧
      ((closeControl scope suffix).erase.append outer).resolve effectInst = some (.builtin identity) := by
  obtain ⟨retained, callable, bound⟩ := plan_invocation_contract position typed
  rcases List.mem_append.mp (bound request) with provided | outward
  · exact Or.inr (plan_provided_resolves provided scope outer)
  · exact Or.inl outward

/-- Structural type/effect evidence for the concrete close plan joins the
    existing independent support, interpretation, and ownership checks. -/
structure DisposalTyped (signature : Signature) (closing : List Instance)
    (cap surviving : Stack) (plan : List CloseEntry) : Prop where
  build : makePlan cap = some plan
  close : Discardable cap.erase surviving.erase (plan.map CloseEntry.erase)
  calls : PlanTyped signature closing plan

namespace Examples

/-- Empty user declarations still authenticate the concrete cell operations. -/
def cellOnly : Signature := withCellSignatures (fun _ _ => none)

theorem cell_only_supported : SignatureSupported cellOnly :=
  cell_signatures_supported _ (by intros; contradiction)

def readClosure : Expr := .lambda 0 (.perform (.cell 4) 0 (.resourceRef 4))

theorem read_closure_typed : Typed cellOnly TypeEnv.empty .none [] readClosure
    (.function .unit .integer [.cell 4] [4]) := by
  apply Typed.lambda
  · exact .perform rfl (by simp) .reference
  · simp [retainedSupport, without, Expr.dependencies, instanceDependencies, Instance.resources]

/-- Hiding a resource dependency behind an otherwise ordinary arrow fails. -/
theorem read_closure_cannot_hide_support :
    ¬ Typed cellOnly TypeEnv.empty .none [] readClosure (.function .unit .integer [.cell 4] []) := by
  intro typed
  cases typed with
  | lambda body retained =>
      have missing := retained (a := 4) (by
        simp [retainedSupport, without, Expr.dependencies, instanceDependencies, Instance.resources])
      simp at missing

/-- Even a closure that merely returns a handle, with no latent operation,
    must retain its resource support in the annotation. -/
theorem pure_handle_closure_cannot_hide_support :
    ¬ Typed cellOnly TypeEnv.empty .none [] (.lambda 0 (.resourceRef 4))
      (.function .unit (.reference 4) [] []) := by
  intro typed
  cases typed with
  | lambda body retained =>
      have missing := retained (a := 4) (by simp [retainedSupport, without, Expr.dependencies])
      simp at missing

/-- Scoped return rejects a closure with a retained local cell. -/
theorem resource_cannot_return_read_closure :
    ¬ Typed cellOnly TypeEnv.empty .none [] (.resource 4 (.integer 0) readClosure)
      (.function .unit .integer [.cell 4] [4]) := by
  intro typed
  cases typed with
  | resource initializer body noEscape noEffectEscape effects => simp [Ty.resources, Instance.resources] at noEscape

theorem integer_scope_typed :
    Typed cellOnly TypeEnv.empty .none [] (.resource 4 (.integer 0) (.integer 42)) .integer :=
  .resource (residual := []) .integer .integer (by simp [Ty.resources]) (by simp) (by simp)

theorem resource_cannot_return_own_handle :
    ¬ Typed cellOnly TypeEnv.empty .none [] (.resource 4 (.integer 0) (.resourceRef 4)) (.reference 4) := by
  intro typed
  cases typed with
  | resource initializer body noEscape noEffectEscape effects => simp [Ty.resources] at noEscape

def scopedRequest : Instance := .user 1 [.resource 5]
def scopedSignature : Signature := fun effectInst operation =>
  if effectInst = scopedRequest ∧ operation = 0 then some (.reference 5, .unit) else none

theorem scoped_signature_supported : SignatureSupported scopedSignature := by
  intro effectInst operation input output found
  simp only [scopedSignature] at found
  split at found
  · rename_i same
    rcases same with ⟨rfl, rfl⟩
    cases found
    simp [Ty.resources, scopedRequest, Instance.resources, TypeArgument.resources]
  · cases found

def scopedHandler : HandlerData :=
  ⟨8, scopedRequest, Execution.Examples.clauses, .none, .unit, by
    simp [Execution.Examples.clauses, ticketDependencies, Clauses.dependencies, Expr.dependencies, without]⟩
def outerCell : Stack := .push (.cell 5 0 .none .unit) .nil
def innerCapture : Stack := .push (.cell 4 0 .none .unit) (.push (.handler scopedHandler) .nil)

theorem typed_outer_payload_crosses_inner_capture :
    resourceDependencies (Expr.resourceRef 5).dependencies ⊆ outerCell.erase.visible ++ [] := by
  have select : HandlerCut scopedRequest (innerCapture.append outerCell) innerCapture outerCell scopedHandler :=
    .push _ _ _ _ _ (by simp [ExecFrame.erase, Frame.target, scopedRequest]) (.hit scopedHandler outerCell rfl)
  have support : Supported (innerCapture.append outerCell).erase [] := by
    apply Supported.push
    · apply Supported.push
      · exact .push _ _ _ (.nil []) (by simp [ExecFrame.erase])
      · simp [scopedHandler, HandlerData.erase, scopedRequest, Instance.resources, TypeArgument.resources,
          Execution.Examples.clauses, Clauses.dependencies, Expr.dependencies, without, resourceDependencies,
          outerCell, Stack.erase, ExecFrame.erase, Control.visible, Frame.visible]
    · simp [ExecFrame.erase]
  exact typed_payload_crosses_cut (operation := 0) (output := .unit) (Typed.reference (signature := scopedSignature)
    (environment := TypeEnv.empty) (ticket := .none) (allowed := []))
    (Execution.Examples.closed_reference 5) (by simp [scopedSignature]) scoped_signature_supported select support

/-- A resource-free effect identity can carry a callable retaining a resource.
    General boundary support admits it; SignatureSupported would not. -/
theorem callable_payload_uses_boundary_support :
    resourceDependencies readClosure.dependencies ⊆
      (Stack.push (.cell 4 0 .none .unit) .nil).erase.visible ++ [] := by
  exact typed_payload_at_boundary read_closure_typed
    (by simp [readClosure, ClosedValue, Expr.IsValue, Expr.dependencies, without,
      instanceDependencies, Instance.resources])
    (by simp [Ty.resources, Instance.resources, Stack.erase, ExecFrame.erase, Control.visible, Frame.visible])

theorem resource_free_callable_signature_exceeds_shortcut :
    ¬ SignatureSupported (fun effectInst operation =>
      if effectInst = Instance.user 1 [] ∧ operation = 0
      then some (.function .unit .integer [.cell 4] [4], .unit) else none) := by
  intro supported
  have bound := supported (.user 1 []) 0 (.function .unit .integer [.cell 4] [4]) .unit (by simp)
  have impossible := bound (a := 4) (by simp [Ty.resources, Instance.resources])
  simp [Instance.resources] at impossible

theorem resource_outward_effect_rejected :
    ¬ Typed (fun _ _ => some (.unit, .unit)) TypeEnv.empty .none [.user 1 [.resource 4]]
      (.resource 4 (.integer 0) (.perform (.user 1 [.resource 4]) 0 .unit)) .unit := by
  intro typed
  cases typed with
  | resource initializer body noEscape noEffectEscape effects =>
      cases body with
      | perform known available operand =>
          have present : Instance.user 1 [.resource 4] ∈ _ :=
            (List.mem_cons.mp available).resolve_left (by simp)
          exact noEffectEscape (List.mem_flatMap.mpr
            ⟨.user 1 [.resource 4], present, by simp [Instance.resources, TypeArgument.resources]⟩)

/-- The disposal plan from the expression machine has a checked callable row. -/
theorem cell_disposal_plan_typed : PlanTyped cellOnly [] Execution.Examples.closePlan := by
  apply PlanTyped.invoke (retained := [4])
  · apply Typed.lambda
    · apply Typed.bind (input := .integer)
      · exact .perform rfl (by simp [Execution.Examples.readAction]) .reference
      · exact .unit
    · simp [Execution.Examples.readBody,
        retainedSupport, without, Expr.dependencies, instanceDependencies, Instance.resources]
  · simp [Execution.Examples.readAction, planProvides]
  · exact .release .nil

/-- Without a retained cell suffix, the same callback cannot claim pure close. -/
theorem disposal_without_cell_cannot_hide_effect :
    ¬ PlanTyped cellOnly [] [.invoke Execution.Examples.readAction] := by
  intro typed
  obtain ⟨retained, callable, effects⟩ := plan_invocation_contract InvocationAt.here typed
  have impossible := effects (a := .cell 4) (by simp [Execution.Examples.readAction])
  simp [planProvides] at impossible

/-- A cell released before invocation does not provide its interpreter there. -/
theorem release_before_callback_rejected :
    ¬ PlanTyped cellOnly [] [.release 4 17, .invoke Execution.Examples.readAction] := by
  intro typed
  cases typed with
  | release rest => exact disposal_without_cell_cannot_hide_effect rest

theorem disposal_read_application_typed :
    Typed cellOnly TypeEnv.empty .none [.cell 4]
      (.app Execution.Examples.readAction.action .unit) .unit :=
  disposal_invocation_typed cell_disposal_plan_typed InvocationAt.here

/-- Empty outward effects coexist with a cell request interpreted in the
    retained suffix, and with the original structural close admission. -/
theorem pure_cell_disposal_typed : DisposalTyped cellOnly [] Execution.Examples.abandoned
    (.spent 3 .unit .none .nil) Execution.Examples.closePlan :=
  ⟨rfl, Execution.Examples.cell_cleanup_disposal_is_admitted, cell_disposal_plan_typed⟩

/-- Retained lexical values contribute support even when the closure's ordinary
    argument/result types and latent effects contain no resource identity. -/
theorem lexical_capture_typed :
    Typed cellOnly (TypeEnv.empty.extend 9 (.reference 4)) .none []
      (.lambda 0 (.bind 1 (.variable 9) .unit)) (.function .unit .unit [] [4]) := by
  apply Typed.lambda
  · apply Typed.bind (input := .reference 4)
    · exact .variable (by simp [TypeEnv.extend])
    · exact .unit
  · simp [retainedSupport, without, Expr.dependencies, TypeEnv.extend, Ty.resources]

theorem lexical_capture_cannot_hide_support :
    ¬ Typed cellOnly (TypeEnv.empty.extend 9 (.reference 4)) .none []
      (.lambda 0 (.bind 1 (.variable 9) .unit)) (.function .unit .unit [] []) := by
  intro typed
  cases typed with
  | lambda body retained =>
      have missing := retained (a := 4) (by
        simp [retainedSupport, without, Expr.dependencies, TypeEnv.extend, Ty.resources])
      simp at missing

end Examples

end Ash.OneShot.Typing

#print axioms Ash.OneShot.Typing.typed_value_support
#print axioms Ash.OneShot.Typing.typed_return_excludes_resource
#print axioms Ash.OneShot.Typing.typed_payload_crosses_cut

#print axioms Ash.OneShot.Typing.context_plug_typed
#print axioms Ash.OneShot.Typing.typed_focus_decomposition
#print axioms Ash.OneShot.Typing.focus_constructs_typed_frame

#print axioms Ash.OneShot.Typing.cell_signatures_supported
#print axioms Ash.OneShot.Typing.typed_function_value
#print axioms Ash.OneShot.Typing.covered_operation_selects_clause
#print axioms Ash.OneShot.Typing.selected_clause_typed
#print axioms Ash.OneShot.Typing.Examples.read_closure_typed
#print axioms Ash.OneShot.Typing.Examples.resource_cannot_return_own_handle
#print axioms Ash.OneShot.Typing.Examples.typed_outer_payload_crosses_inner_capture

#print axioms Ash.OneShot.Typing.typed_payload_at_boundary
#print axioms Ash.OneShot.Typing.disposal_invocation_typed
#print axioms Ash.OneShot.Typing.Examples.cell_disposal_plan_typed
#print axioms Ash.OneShot.Typing.Examples.disposal_without_cell_cannot_hide_effect

#print axioms Ash.OneShot.Typing.plan_provided_resolves
#print axioms Ash.OneShot.Typing.plan_request_is_outward_or_interpreted
#print axioms Ash.OneShot.Typing.Examples.pure_cell_disposal_typed
#print axioms Ash.OneShot.Typing.Examples.release_before_callback_rejected

#print axioms Ash.OneShot.Typing.Examples.lexical_capture_cannot_hide_support
