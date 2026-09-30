import Joint

/-!
Deriving local access admission from the joint invariant and actual control.
Release is justified by result typing. Capture has a general boundary-support
route and a restricted signature-supported route. The latter is sufficient,
not mandatory for resource-retaining callable payloads. Disposal compatibility
and source-derived admission of future cuts remain separate obligations.
-/

namespace Ash.OneShot.Admission
open Syntax Execution Typing Joint

/-- Typed cell return supplies the release field of access admission. -/
theorem release_check_from_typing
    (typed : EffectConfigurationTyped signature tickets before result outgoing)
    (same : before = ⟨value, scope, .push (.cell identity payload savedScope answer) tail⟩)
    (closed : ClosedValue value) : identity ∉ resourceDependencies value.dependencies := by
  rw [same] at typed
  exact typed_cell_return_excludes_identity (effect_configuration_has_types typed) closed

/-- A general operand type may retain resources that are absent from the effect
    identity. Check those resources at the actual outside boundary. -/
theorem capture_check_from_type_boundary {tail : Stack}
    (typed : EffectConfigurationTyped signature tickets
      ⟨.perform requested operation operand, scope, whole⟩ result outgoing)
    (operationType : signature requested operation = some (input, output))
    (closed : ClosedValue operand)
    (boundary : input.resources ⊆ tail.erase.visible ++ ambient) :
    resourceDependencies operand.dependencies ⊆ tail.erase.visible ++ ambient := by
  obtain ⟨type, effects, expression, ports, control⟩ := typed
  cases expression with
  | checked scope expression => cases expression with
      | perform actual available operandTyped =>
          have same := Option.some.inj (actual.symm.trans operationType)
          cases same
          exact typed_payload_at_boundary operandTyped closed boundary

/-- The restricted signature condition derives that payload check for any
    actual selected handler whose retained control is supported. -/
theorem capture_check_from_supported_signature
    (typed : EffectConfigurationTyped signature tickets
      ⟨.perform requested operation operand, scope, whole⟩ result outgoing)
    (supported : SignatureSupported signature)
    (cut : HandlerCut requested whole cap tail handler)
    (controlSupport : Supported whole.erase ambient)
    (closed : ClosedValue operand) :
    resourceDependencies operand.dependencies ⊆ tail.erase.visible ++ ambient := by
  obtain ⟨type, effects, expression, ports, control⟩ := typed
  cases expression with
  | checked scope expression => cases expression with
      | perform operationType available operandTyped =>
          exact typed_payload_crosses_cut operandTyped closed operationType supported cut controlSupport

/-- Exact cut uniqueness transports one concrete payload-support derivation
    to the capture field required by the existing execution admission. -/
theorem selected_capture_access_checks
    (selected : HandlerCut requested whole cap tail handler)
    (payload : resourceDependencies operand.dependencies ⊆ tail.erase.visible ++ ambient) :
    AccessChecks ⟨.perform requested operation operand, scope, whole⟩ ambient := by
  constructor
  · intro identity stored answer savedScope current value outside same closed
    cases same
    exact False.elim closed.1
  · intro target operation argument current wholeStack capture outside provider same cut closed
    cases same
    have sameCut := cut_unique (sourceCut_is_cut (handler_cut_erases selected))
      (sourceCut_is_cut (handler_cut_erases cut))
    simpa only [sameCut.2] using payload
  · intro binder owner current caller input answer front capture outside plan same
    cases same

theorem selected_type_boundary_access_checks
    (typed : EffectConfigurationTyped signature tickets
      ⟨.perform requested operation operand, scope, whole⟩ result outgoing)
    (operationType : signature requested operation = some (input, output))
    (selected : HandlerCut requested whole cap tail handler) (closed : ClosedValue operand)
    (boundary : input.resources ⊆ tail.erase.visible ++ ambient) :
    AccessChecks ⟨.perform requested operation operand, scope, whole⟩ ambient :=
  selected_capture_access_checks selected (capture_check_from_type_boundary typed operationType closed boundary)

/-- Neither a closed value nor its return step can be a capture or discard. -/
theorem value_access_checks
    (typed : EffectConfigurationTyped signature tickets before result outgoing)
    (closed : ClosedValue before.expression) : AccessChecks before ambient := by
  constructor
  · intro identity payload answer savedScope scope value tail same valueClosed
    exact release_check_from_typing typed same valueClosed
  · intro requested operation operand scope whole cap tail handler same cut valueClosed
    rw [same] at closed
    exact False.elim closed.1
  · intro binder owner scope caller input answer front cap tail plan same
    rw [same] at closed
    exact False.elim closed.1

/-- Focus proves the whole expression is not a value and any focused request
    operand is not a value. No capture boundary is crossed by this step. -/
theorem focus_access_checks (focus : Focus whole child context) :
    AccessChecks ⟨whole, scope, stack⟩ ambient := by
  constructor
  · intro identity payload answer savedScope current value tail same closed
    have equal : whole = value := congrArg Configuration.expression same
    exact False.elim (focus_is_not_value focus (equal.symm ▸ closed.1))
  · intro requested operation operand current wholeStack cap tail handler same cut closed
    cases focus <;> cases same
    rename_i notValue
    exact False.elim (notValue closed.1)
  · intro binder owner current caller input answer front cap tail plan same
    cases focus <;> cases same

/-- Actual builtin selection blocks a source-handler cut for that instance. -/
theorem builtin_request_access_checks (update : CellUpdate identity old new before after) :
    AccessChecks ⟨.perform (.cell identity) operation operand, scope, before⟩ ambient := by
  constructor
  · intro resource payload answer savedScope current value tail same closed
    cases same
    exact False.elim closed.1
  · intro requested operation argument current whole cap tail handler same cut closed
    cases same
    exact False.elim (Syntax.UsageExecutionExamples.cell_update_excludes_handler_cut update cut)
  · intro binder owner current caller input answer front cap tail plan same
    cases same

theorem ordinary_access_checks (step : OrdinaryStep before after) : AccessChecks before ambient := by
  cases step with
  | bind | beta | ifTrue | ifFalse =>
      apply Syntax.UsageExecutionExamples.ordinary_access_checks
      · simp [Expr.IsValue]
      · intro requested operation operand same; cases same
      · intro binder same; cases same
  | read cell => exact builtin_request_access_checks cell
  | write cell => exact builtin_request_access_checks cell

/-- Complete nondiscard access admission for the signature-supported fragment.
    General signatures retain the boundary-support route above. -/
theorem supported_signature_access_checks
    (valid : Valid signature policy registry ambient before result outgoing)
    (supported : SignatureSupported signature)
    (notDiscard : ∀ binder, before.execution.configuration.expression ≠ .discard binder) :
    AccessChecks before.execution.configuration ambient := by
  constructor
  · intro identity payload answer savedScope scope value tail same closed
    exact release_check_from_typing valid.effects same closed
  · intro requested operation operand scope whole cap tail handler same cut closed
    have typed := valid.effects
    have support := valid.support.control
    rw [same] at typed support
    exact capture_check_from_supported_signature typed supported cut support closed
  · intro binder owner scope caller input answer front cap tail plan same
    exact False.elim (notDiscard binder (congrArg Configuration.expression same))

/-- Joint value preservation no longer needs separately supplied access checks. -/
theorem value_event_preserves
    (raw : RawStep before.execution.configuration after [] discharged)
    (closed : ClosedValue before.execution.configuration.expression)
    (valid : Valid signature policy registry ambient before result outgoing) :
    NamedAccessStep ambient before (advanceState before after [] discharged) ∧
    Valid signature policy registry ambient (advanceState before after [] discharged) result outgoing :=
  value_event_preserves_joint_configuration raw closed valid (value_access_checks valid.effects closed)

theorem ordinary_step_preserves
    (step : OrdinaryStep before.execution.configuration after)
    (valid : Valid (withCellSignatures users) policy registry ambient before result outgoing) :
    NamedAccessStep ambient before (advanceState before after [] []) ∧
    Valid (withCellSignatures users) policy registry ambient (advanceState before after [] []) result outgoing :=
  ordinary_step_preserves_joint_configuration step valid (ordinary_access_checks step)

theorem focus_constructs
    (valid : Valid signature policy registry ambient
      ⟨⟨⟨whole, scope, tail⟩, issued, completed⟩, activations⟩ result outgoing)
    (focus : Focus whole child context) :
    ∃ plain : PlainData, plain.context = context ∧ plain.scope = scope ∧
      let initial : NamedState := ⟨⟨⟨whole, scope, tail⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨child, scope, .push (.plain plain) tail⟩
      NamedAccessStep ambient initial (advanceState initial after [] []) ∧
      Valid signature policy registry ambient (advanceState initial after [] []) result outgoing :=
  focus_constructs_joint_configuration valid focus (focus_access_checks focus)

/-- A closing callback either resolves within both retained prefixes to the
    same interpreter, or delegates through both to a declared outside request. -/
inductive OpenRequests (original surviving : Control) (outward : List Instance) : List Instance → Prop where
  | nil : OpenRequests original surviving outward []
  | localTarget (request : Instance) (rest : List Instance) (target : Target)
      (before : original.resolve request = some target) (after : surviving.resolve request = some target)
      (next : OpenRequests original surviving outward rest) :
      OpenRequests original surviving outward (request :: rest)
  | outside (request : Instance) (rest : List Instance)
      (before : original.resolve request = none) (after : surviving.resolve request = none)
      (declared : request ∈ outward) (next : OpenRequests original surviving outward rest) :
      OpenRequests original surviving outward (request :: rest)

theorem open_requests_materialize (checked : OpenRequests original surviving outward requests)
    (provided : RequestsResolved outer outward) :
    SameRequests (original.append outer) (surviving.append outer) requests := by
  induction checked with
  | nil => exact .nil
  | localTarget request rest target before after next ih =>
      exact .cons request rest target (by simp [resolve_append, before]) (by simp [resolve_append, after]) ih
  | outside request rest before after declared next ih =>
      obtain ⟨target, found⟩ := provided request declared
      exact .cons request rest target (by simp [resolve_append, before, found])
        (by simp [resolve_append, after, found]) ih

/-- Structural closing with an explicit outside resource/request interface.
    The rules inspect actual callback dependencies and both materialized
    prefixes. Protected running/completion frames have no rule. -/
inductive OpenCloses : Control → Control → Control → List Nat → List Instance → List CloseItem → Prop where
  | nil (original surviving : Control) (resources : List Nat) (outward : List Instance) :
      OpenCloses .nil original surviving resources outward []
  | bind (frame : Frame) (rest original surviving : Control) (resources : List Nat)
      (outward : List Instance) (plan : List CloseItem) (kind : frame.kind = .bind)
      (next : OpenCloses rest original surviving resources outward plan) :
      OpenCloses (.push frame rest) original surviving resources outward plan
  | handler (frame : Frame) (effectInst : Instance) (activation : Nat) (rest original surviving : Control)
      (resources : List Nat) (outward : List Instance) (plan : List CloseItem)
      (kind : frame.kind = .handler effectInst activation)
      (next : OpenCloses rest original surviving resources outward plan) :
      OpenCloses (.push frame rest) original surviving resources outward plan
  | resource (frame : Frame) (identity : Nat) (rest original surviving : Control) (resources : List Nat)
      (outward : List Instance) (plan : List CloseItem) (kind : frame.kind = .resource identity)
      (next : OpenCloses rest original surviving resources outward plan) :
      OpenCloses (.push frame rest) original surviving resources outward (.release identity :: plan)
  | armed (frame : Frame) (identity : Nat) (rest original surviving : Control) (resources : List Nat)
      (outward : List Instance) (plan : List CloseItem) (kind : frame.kind = .armed identity)
      (ticketClosed : frame.pending = [])
      (access : frame.access ⊆ ((planControl plan).append surviving).visible ++ resources)
      (requests : OpenRequests (rest.append original) ((planControl plan).append surviving) outward frame.requests)
      (next : OpenCloses rest original surviving resources outward plan) :
      OpenCloses (.push frame rest) original surviving resources outward
        (.invoke identity frame.access frame.requests :: plan)
  | live (owner : Nat) (input answer : Ty) (saved rest original surviving : Control) (resources : List Nat)
      (outward : List Instance) (inside outside : List CloseItem)
      (capture : OpenCloses saved (rest.append original) ((planControl outside).append surviving) resources outward inside)
      (next : OpenCloses rest original surviving resources outward outside) :
      OpenCloses (.live owner input answer saved rest) original surviving resources outward
        (inside ++ .retire owner :: outside)
  | spent (owner : Nat) (answer : Ty) (rest original surviving : Control) (resources : List Nat)
      (outward : List Instance) (plan : List CloseItem)
      (next : OpenCloses rest original surviving resources outward plan) :
      OpenCloses (.spent owner answer rest) original surviving resources outward plan

theorem open_closes_materialize
    (checked : OpenCloses capture original surviving resources outward plan)
    (access : resources ⊆ outer.visible) (requests : RequestsResolved outer outward) :
    Closes capture (original.append outer) (surviving.append outer) plan := by
  induction checked with
  | nil original surviving resources outward => exact .nil _ _
  | bind frame rest original surviving resources outward plan kind next ih =>
      exact .bind frame rest _ _ plan kind (ih access requests)
  | handler frame effectInst activation rest original surviving resources outward plan kind next ih =>
      exact .handler frame effectInst activation rest _ _ plan kind (ih access requests)
  | resource frame identity rest original surviving resources outward plan kind next ih =>
      exact .resource frame identity rest _ _ plan kind (ih access requests)
  | armed frame identity rest original surviving resources outward plan kind ticketClosed support routes next ih =>
      refine .armed frame identity rest _ _ plan kind ticketClosed ?_ ?_ (ih access requests)
      · intro identity retained
        have member := support retained
        rcases List.mem_append.mp member with localResource | outsideResource
        · simpa only [visible_append, List.append_assoc] using List.mem_append_left outer.visible localResource
        · simpa only [visible_append, List.append_assoc] using
            List.mem_append_right ((planControl plan).append surviving).visible (access outsideResource)
      · simpa only [append_assoc] using open_requests_materialize routes requests
  | live owner input answer saved rest original surviving resources outward inside outside capture next ihCapture ihNext =>
      exact .live owner input answer saved rest _ _ inside outside
        (by simpa only [append_assoc] using ihCapture access requests) (ihNext access requests)
  | spent owner answer rest original surviving resources outward plan next ih =>
      exact .spent owner answer rest _ _ plan (ih access requests)

/-- Extending caller control preserves availability of an outside interface.
    It may change an outside interpreter, but both closing prefixes see the
    same caller, so their exact-interpretation agreement is preserved. -/
theorem requests_resolved_under_prefix (provided : RequestsResolved outer outward) (front : Control) :
    RequestsResolved (front.append outer) outward := by
  intro request member
  cases found : front.resolve request with
  | some target => exact ⟨target, by simp [resolve_append, found]⟩
  | none =>
      obtain ⟨target, outside⟩ := provided request member
      exact ⟨target, by simp [resolve_append, found, outside]⟩

theorem open_discardable_under_caller_prefix
    (checked : OpenCloses capture .nil .nil resources outward plan)
    (internal : InternalUses capture.liveTickets capture.pending)
    (access : resources ⊆ outer.visible) (requests : RequestsResolved outer outward) (front : Control) :
    Discardable capture (front.append outer) plan := by
  refine .checked (open_closes_materialize (outer := front.append outer) checked ?_ (requests_resolved_under_prefix requests front)) internal
  intro identity retained
  simpa only [visible_append] using List.mem_append_right front.visible (access retained)

/-- Resources retained by the capture but owned outside it. This interface is
    computed from existing dependency and ownership inventories. -/
def outsideResources (capture : Control) : List Nat :=
  (retainedResources capture).filter fun identity => decide (Owner.resource identity ∉ capture.owners)

theorem outside_resources_supported (support : Supported capture ambient) :
    outsideResources capture ⊆ ambient := by
  intro identity retained
  obtain ⟨dependency, external⟩ := List.mem_filter.mp retained
  have unowned : Owner.resource identity ∉ capture.owners := of_decide_eq_true external
  rcases retained_resource_supported support dependency with outside | owned
  · exact outside
  · exact False.elim (unowned owned)

/-- A checked, actual disposal plan with an outside interface. The plan holds
    code and evidence; executing it still requires the unique live owner. -/
structure PreparedDisposal (signature : Signature) (closingEffects : List Instance) (capture : Stack) where
  plan : List CloseEntry
  built : makePlan capture = some plan
  typed : PlanTyped signature closingEffects plan
  closing : OpenCloses capture.erase .nil .nil (outsideResources capture.erase) closingEffects
    (plan.map CloseEntry.erase)
  internal : InternalUses capture.erase.liveTickets capture.erase.pending

theorem prepared_disposal_under_caller_prefix
    (prepared : PreparedDisposal signature closingEffects capture)
    (support : Supported capture.erase outer.visible) (requests : RequestsResolved outer closingEffects)
    (front : Control) :
    Discardable capture.erase (front.append outer) (prepared.plan.map CloseEntry.erase) :=
  open_discardable_under_caller_prefix prepared.closing prepared.internal
    (outside_resources_supported support) requests front

/-- The dormant capture's external resources remain supplied by its actual
    outer tail; newly installed clause-prefix resources are unnecessary. -/
theorem saved_capture_outside_support {front capture tail : Stack}
    (support : Supported (front.append (.live owner input answer capture caller tail)).erase []) :
    Supported capture.erase tail.erase.visible := by
  rw [erase_append] at support
  obtain ⟨inside, outside⟩ := supported_decompose front.erase support
  cases outside with
  | live owner input answer saved rest ambient checked tailChecked => simpa using checked

/-- Closed effect interfaces supply every declared closing request at the
    active live boundary, excluding the dormant capture from lookup. -/
theorem live_close_requests {front capture tail : Stack}
    (typed : EffectConfigurationTyped signature tickets
      ⟨expression, scope, front.append (.live owner input answer capture caller tail)⟩ result [])
    (known : tickets owner = some contract) : RequestsResolved tail.erase contract.closeEffects := by
  obtain ⟨type, effects, code, ports, control⟩ := typed
  obtain ⟨middle, inside, outside⟩ := effect_stack_decompose front control
  cases outside with
  | live actual callerScope saved rest resume close bound =>
      have same := Option.some.inj (known.symm.trans actual)
      cases same
      intro request member
      rcases effect_stack_provides_or_exports rest (close member) with provided | impossible
      · exact provided
      · cases impossible

/-- For a closed joint state, the existing support/effect fields supply the
    prepared plan's outside interface. No outside-support oracle is added. -/
theorem prepared_disposal_at_live_boundary {front capture tail : Stack}
    (valid : Valid signature policy registry []
      ⟨⟨⟨expression, scope, front.append (.live owner input answer capture caller tail)⟩,
        issued, completed⟩, activations⟩ result [])
    (known : registry.effects owner = some contract)
    (prepared : PreparedDisposal signature contract.closeEffects capture) :
    Discardable capture.erase (front.erase.append (.spent owner answer tail.erase))
      (prepared.plan.map CloseEntry.erase) := by
  apply prepared_disposal_under_caller_prefix prepared (outer := .spent owner answer tail.erase)
  · exact saved_capture_outside_support valid.support.control
  · exact live_close_requests valid.effects known

/-- Every retained live boundary whose record permits disposal carries a
    structural plan certificate. Resume-only captures need no such certificate.
    Establishing this judgment from source checking is open. Local execution
    preservation is proved separately in PreparedExecution.lean. -/
inductive PreparedCaptures (signature : Signature) (registry : Registry) : Stack → Prop where
  | nil : PreparedCaptures signature registry .nil
  | push (rest : PreparedCaptures signature registry tail) :
      PreparedCaptures signature registry (.push frame tail)
  | live (known : registry owner = some record)
      (ready : record.permissions.dispose = true →
        Nonempty (PreparedDisposal signature record.contract.closeEffects capture))
      (saved : PreparedCaptures signature registry capture)
      (rest : PreparedCaptures signature registry tail) :
      PreparedCaptures signature registry (.live owner input answer capture caller tail)
  | spent (rest : PreparedCaptures signature registry tail) :
      PreparedCaptures signature registry (.spent owner answer caller tail)

theorem prepared_captures_tail {front tail : Stack}
    (checked : PreparedCaptures signature registry (front.append tail)) :
    PreparedCaptures signature registry tail := by
  induction front with
  | nil => exact checked
  | push frame rest ih => cases checked with
      | push next => exact ih next
  | live owner input answer saved caller rest ihSaved ihRest => cases checked with
      | live known ready savedChecked restChecked => exact ihRest restChecked
  | spent owner answer caller rest ih => cases checked with
      | spent restChecked => exact ih restChecked

theorem discard_code_permission {registry : Registry}
    (code : CodeDemand policy registry.usage scope (.discard binder) demand)
    (resolved : scope.resolve binder = some owner) :
    ∃ rights, registry.usage owner = some rights ∧ rights.dispose = true := by
  cases code with
  | idle scope checked => cases checked
  | consume known checked => cases checked with
      | discard permitted =>
          simp [Scope.resolve] at resolved
          subst owner
          exact ⟨_, known, permitted⟩

/-- Independent permission checking selects the certificate at the actual
    live boundary, using the same historical record for both facets. -/
theorem prepared_capture_for_discard {front capture tail : Stack}
    (checked : PreparedCaptures signature registry
      (front.append (.live owner input answer capture caller tail)))
    (code : CodeDemand policy registry.usage scope (.discard binder) demand)
    (resolved : scope.resolve binder = some owner) :
    ∃ record, registry owner = some record ∧
      Nonempty (PreparedDisposal signature record.contract.closeEffects capture) := by
  have boundary := prepared_captures_tail checked
  cases boundary with
  | live known ready saved rest =>
      obtain ⟨rights, usageKnown, permitted⟩ := discard_code_permission code resolved
      rw [Registry.usage, known] at usageKnown
      have same := Option.some.inj usageKnown
      exact ⟨_, known, ready (same ▸ permitted)⟩

/-- A current discard derives its access checks from retained certificates.
    Plan existence is stored in those certificates, not assumed by this rule. -/
theorem prepared_discard_access_checks
    (valid : Valid signature policy registry []
      ⟨⟨⟨.discard binder, scope, stack⟩, issued, completed⟩, activations⟩ result [])
    (prepared : PreparedCaptures signature registry stack) :
    AccessChecks ⟨.discard binder, scope, stack⟩ [] := by
  constructor
  · intro identity payload answer savedScope current value tail same closed
    cases same
    exact False.elim closed.1
  · intro requested operation operand current whole capture tail handler same
    cases same
  · intro other owner current caller input answer front capture tail plan same resolved built
    cases same
    obtain ⟨currentDemand, controlDemand, code, control, accessible, balance, unique⟩ := valid.usage
    obtain ⟨record, known, ⟨certificate⟩⟩ := prepared_capture_for_discard prepared code resolved
    have effectKnown : registry.effects owner = some record.contract := by simp [Registry.effects, known]
    have compatible := prepared_disposal_at_live_boundary valid effectKnown certificate
    have samePlan := Option.some.inj (certificate.built.symm.trans built)
    simpa only [samePlan] using compatible

namespace Examples

def payloadType : Ty := .function .unit (.reference 4) [] [4]
def callableSignature : Signature := fun effectInst operation =>
  if effectInst = .user 1 [] ∧ operation = 0 then some (payloadType, .unit) else none

def payload : Expr := .lambda 0 (.resourceRef 4)
def clauses : Clauses := .cons 0 1 9 (.resume 9 .unit) .nil

theorem clauses_typed : ClausesTyped callableSignature TypeEnv.empty (.user 1 []) .unit [] clauses :=
  .cons (input := payloadType) (output := .unit) (by simp [callableSignature]) (.resume .unit (fun _ used => used)) .nil

def handler : HandlerData := ⟨8, .user 1 [], clauses, .none, .unit, typed_clauses_have_barrier clauses_typed⟩
def outside : Stack := .push (.cell 4 17 .none .unit) .nil
def whole : Stack := .push (.handler handler) outside

theorem handler_effects : EffectFrame callableSignature tickets (.handler handler) [.user 1 []] [] := by
  apply EffectFrame.handler ⟨_, .none⟩ clauses_typed
  · intro operation input output found
    simp only [handler, callableSignature] at found
    split at found
    · rename_i equal
      simp [handler, clauses, clauseKeys, equal.2]
    · cases found
  · decide

theorem payload_typed : Typed callableSignature TypeEnv.empty .none [] payload payloadType := by
  apply Typed.lambda
  · exact .reference
  · simp [retainedSupport, Expr.dependencies, without]

theorem request_typed : EffectConfigurationTyped callableSignature tickets
    ⟨.perform (.user 1 []) 0 payload, .none, whole⟩ .unit [] := by
  refine ⟨.unit, [.user 1 []], .checked .none
    (.perform (by simp [callableSignature]) (by simp)
      (typed_value_transport payload_typed (by trivial) .none _)), ?_, ?_⟩
  · exact .push (effect_frame_has_types handler_effects)
      (.push (.cell ⟨_, .none⟩ (by simp [Ty.resources])) .nil)
  · exact .push handler_effects
      (.push (.cell ⟨_, .none⟩ (by simp [Ty.resources])) (.nil (fun _ used => used)) (by simp))
      (fun _ used => used)

/-- A callable retains a cell outside the cut. Its signature does not satisfy
    the shortcut, but the actual boundary check admits this payload. -/
theorem general_callable_payload_is_admitted :
    ¬ SignatureSupported callableSignature ∧
    AccessChecks ⟨.perform (.user 1 []) 0 payload, .none, whole⟩ [] := by
  constructor
  · intro supported
    have impossible := supported (.user 1 []) 0 payloadType .unit (by simp [callableSignature])
      (a := 4) (by simp [payloadType, Ty.resources])
    simp [Instance.resources] at impossible
  · apply selected_type_boundary_access_checks (tickets := fun _ => none)
      (input := payloadType) (output := .unit) request_typed
      (by simp [callableSignature]) (HandlerCut.hit handler outside rfl)
      (typed_value_is_closed payload_typed (by trivial))
    simp [payloadType, Ty.resources, outside, Stack.erase, ExecFrame.erase, Control.visible, Frame.visible]

end Examples

namespace ClosingExamples
open Execution.Examples

/-- This capture closes without requiring resources or requests from callers:
    the callback reads the cell retained in its actual plan suffix. -/
theorem cell_open_closing : OpenCloses abandoned.erase .nil .nil [] []
    (closePlan.map CloseEntry.erase) := by
  refine .armed readAction.erase 7 _ .nil .nil [] [] [.release 4] rfl rfl ?_ ?_ ?_
  · simp [readAction, ActionData.erase, readCallback, readBody, Expr.dependencies,
      instanceDependencies, Instance.resources, resourceDependencies, without,
      planControl, CloseItem.frame, Control.visible, Frame.visible]
  · exact .localTarget (.cell 4) [] (.builtin 4) rfl rfl .nil
  · exact .resource _ 4 _ _ _ [] [] [] rfl
      (.handler discardHandler.erase (.user 1 []) 10 _ _ _ [] [] [] rfl (.nil _ _ [] []))

theorem cell_outside_resources_empty : outsideResources abandoned.erase = [] := by
  simp [outsideResources, retainedResources, abandoned, readAction, readCallback, readBody,
    discardHandler, Stack.erase, ExecFrame.erase, ActionData.erase, HandlerData.erase,
    Control.owners, Frame.owners, Expr.dependencies, Clauses.dependencies, resourceDependencies,
    Instance.resources, instanceDependencies, without]

def preparedCell : PreparedDisposal RetainedExamples.userAndCells [] abandoned :=
  ⟨closePlan, rfl,
    .invoke RetainedExamples.read_callback_retained_type
      (by simp [readAction, planProvides]) (.release .nil),
    by rw [cell_outside_resources_empty]; exact cell_open_closing, .nil⟩

theorem prepared_cell_admits_actual_disposal :
    Discardable abandoned.erase (.spent 3 .unit .nil) (closePlan.map CloseEntry.erase) :=
  prepared_disposal_at_live_boundary (front := .nil) Joint.Examples.disposal_initial_valid
    (contract := Joint.Examples.disposalRecord.contract) rfl preparedCell

/-- The exact-interpretation guarantee compares original and closing control
    under the same current caller, including arbitrary added clause control. -/
theorem cell_closing_accepts_any_caller (front outer : Control) :
    Discardable abandoned.erase (front.append outer) (closePlan.map CloseEntry.erase) :=
  open_discardable_under_caller_prefix cell_open_closing .nil (List.nil_subset _)
    (by intro request member; cases member) front

/-- A callback may instead use a genuinely external cell. Both original
    and materialized control delegate the request to their shared caller. -/
theorem outward_cell_open_closing :
    OpenCloses (.push readAction.erase .nil) .nil .nil [4] [.cell 4]
      [.invoke 7 readAction.erase.access readAction.requests] := by
  refine .armed readAction.erase 7 .nil .nil .nil [4] [.cell 4] [] rfl rfl ?_ ?_ (.nil _ _ _ _)
  · simp [readAction, ActionData.erase, readCallback, readBody, Expr.dependencies,
      instanceDependencies, Instance.resources, resourceDependencies, without,
      planControl, Control.visible]
  · exact .outside (.cell 4) [] rfl rfl (by simp) .nil

theorem outward_cell_closing_under_prefix (front : Control) :
    Discardable (.push readAction.erase .nil)
      (front.append (.push (ExecFrame.cell 4 17 .none .unit).erase .nil))
      [.invoke 7 readAction.erase.access readAction.requests] := by
  apply open_discardable_under_caller_prefix outward_cell_open_closing .nil
  · simp [ExecFrame.erase, Control.visible, Frame.visible]
  · intro request member
    simp only [List.mem_singleton] at member
    subst request
    exact ⟨.builtin 4, rfl⟩

end ClosingExamples

namespace DisposalGap
open Execution.Examples
open Joint.Examples (disposalRegistry disposalRecord)
open ControlUsageExamples (policy none_known)

def protectedCapture : Stack := .push (.running readAction .unit closed_unit)
  (.push (.cell 4 17 .none .unit) (.push (.handler discardHandler) .nil))
def initial : NamedState :=
  ⟨⟨⟨.discard 9, closeScope, .live 3 .unit .unit protectedCapture .none .nil⟩,
    [.resource 4, .cleanup 7, .ticket 3], []⟩, [10]⟩

theorem protected_types : StackTyped RetainedExamples.userAndCells tickets protectedCapture .unit .unit := by
  have old := RetainedExamples.abandoned_cell_stack_has_typed_code (tickets := tickets)
  cases old with
  | push frame rest => cases frame with
      | armed scope callable => exact .push (.running scope callable .unit) rest

theorem protected_effects : EffectStack RetainedExamples.userAndCells tickets
    protectedCapture [.cell 4, .user 1 []] [] := by
  have old := Joint.Examples.abandoned_cell_effects (tickets := tickets)
  cases old with
  | push frame rest bound => cases frame with
      | armed scope callable requests => exact .push (.running scope callable .unit requests) rest bound

/-- The six-facet invariant is inhabited even when explicit disposal is not
    operationally ready. This is evidence for the missing admission condition. -/
theorem protected_discard_has_joint_invariant :
    Valid RetainedExamples.userAndCells policy disposalRegistry [] initial .unit [] := by
  constructor
  · exact Joint.Examples.disposal_initial_valid.ledger
  · exact ⟨Joint.Examples.disposal_initial_valid.names.tickets,
      Joint.Examples.disposal_initial_valid.names.handlers, Joint.Examples.disposal_initial_valid.names.unique⟩
  · have old := Joint.Examples.disposal_initial_valid.support
    constructor
    · cases old.control with
      | live owner input answer capture rest ambient saved outside =>
          cases saved with
          | push frame rest ambient next access =>
              refine .live _ _ _ _ _ _ (.push _ _ _ next ?_) outside
              simpa [ExecFrame.erase, Expr.dependencies, resourceDependencies] using access
    · simp [initial, Expr.dependencies, resourceDependencies]
  · exact ⟨.unit, [], .checked (.bound (binder := 9) (contract := disposalRecord.contract) rfl)
      (.discard (fun _ used => used)), .live rfl ⟨_, .none⟩ protected_types .nil,
      .live (contract := disposalRecord.contract) rfl ⟨_, .none⟩ protected_effects
        (.nil (fun _ used => used)) (fun _ used => used) (fun _ used => used) (fun _ used => used)⟩
  · refine ⟨[3], [], .consume rfl (.discard rfl), ?_, ?_, .refl _, by decide⟩
    · refine .live (owner := 3) (captureDemand := []) (restDemand := []) rfl
        (none_known disposalRegistry.usage) ?_ .nil
      exact .push (.running (none_known disposalRegistry.usage)
        (.lambda (.bind (.perform .resourceRef) .unit)) .unit) (List.nil_subset _)
        (.push (.cell (none_known disposalRegistry.usage)) (List.nil_subset _)
          (.push (.handler (none_known disposalRegistry.usage) (.cons (.discard rfl) .nil))
            (List.nil_subset _) .nil))
    · simp [initial, activeTickets]
  · exact Joint.Examples.disposal_initial_valid.registry

theorem protected_discard_has_no_close_plan : makePlan protectedCapture = none := rfl

/-- Current typing, support and usage do not entail the plan-existence premise
    needed to execute an explicit discard. The required strengthening is real. -/
theorem joint_invariant_does_not_establish_disposal_readiness :
    Valid RetainedExamples.userAndCells policy disposalRegistry [] initial .unit [] ∧
    ¬ ∃ plan, makePlan protectedCapture = some plan :=
  ⟨protected_discard_has_joint_invariant, by simp [protected_discard_has_no_close_plan]⟩

theorem protected_discard_cannot_be_prepared :
    ¬ Nonempty (PreparedDisposal RetainedExamples.userAndCells [] protectedCapture) := by
  rintro ⟨prepared⟩
  have built := prepared.built
  rw [protected_discard_has_no_close_plan] at built
  cases built

end DisposalGap

end Ash.OneShot.Admission

#print axioms Ash.OneShot.Admission.release_check_from_typing
#print axioms Ash.OneShot.Admission.capture_check_from_type_boundary
#print axioms Ash.OneShot.Admission.capture_check_from_supported_signature
#print axioms Ash.OneShot.Admission.value_access_checks
#print axioms Ash.OneShot.Admission.focus_access_checks
#print axioms Ash.OneShot.Admission.supported_signature_access_checks
#print axioms Ash.OneShot.Admission.value_event_preserves
#print axioms Ash.OneShot.Admission.ordinary_step_preserves
#print axioms Ash.OneShot.Admission.focus_constructs

#print axioms Ash.OneShot.Admission.selected_type_boundary_access_checks
#print axioms Ash.OneShot.Admission.Examples.general_callable_payload_is_admitted

#print axioms Ash.OneShot.Admission.DisposalGap.joint_invariant_does_not_establish_disposal_readiness

#print axioms Ash.OneShot.Admission.open_requests_materialize
#print axioms Ash.OneShot.Admission.open_closes_materialize
#print axioms Ash.OneShot.Admission.open_discardable_under_caller_prefix

#print axioms Ash.OneShot.Admission.outside_resources_supported
#print axioms Ash.OneShot.Admission.prepared_disposal_at_live_boundary
#print axioms Ash.OneShot.Admission.ClosingExamples.prepared_cell_admits_actual_disposal
#print axioms Ash.OneShot.Admission.DisposalGap.protected_discard_cannot_be_prepared

#print axioms Ash.OneShot.Admission.ClosingExamples.outward_cell_closing_under_prefix
#print axioms Ash.OneShot.Admission.prepared_discard_access_checks
