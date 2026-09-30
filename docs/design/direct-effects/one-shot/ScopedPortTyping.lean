import ScopedSignatureGap

/-!
Declared ports separated from the extra resource support of callable values.
Reference identities and latent exact effect instances remain in port types.
This layer covers the current scoped expression grammar. It is type/effect
checking, not complete source admission: stored support and control boundaries
must be checked independently, including when declared types are resource-free.
-/

namespace Ash.OneShot.ScopedPorts
open Instantiation ScopedExpressions
open ScopedTyping (World)

inductive Port where
  | unit | boolean | integer
  | product : Port → Port → Port
  | reference : Nat → Port
  | function : Port → Port → List Instance → Port
  deriving DecidableEq, Repr

def Port.resources : Port → List Nat
  | .unit | .boolean | .integer => []
  | .product left right => left.resources ++ right.resources
  | .reference identity => [identity]
  | .function input output requests =>
      input.resources ++ output.resources ++ requests.flatMap Instance.resources

def eraseType : Ty → Port
  | .unit => .unit
  | .boolean => .boolean
  | .integer => .integer
  | .reference identity => .reference identity
  | .product left right => .product (eraseType left) (eraseType right)
  | .function input output requests _ => .function (eraseType input) (eraseType output) requests

theorem erasure_preserves_declared_resources (type : Ty) :
    (eraseType type).resources ⊆ type.resources := by
  induction type with
  | unit | boolean | integer | reference => exact List.Subset.refl _
  | product left right ihLeft ihRight => exact append_subset ihLeft ihRight
  | function input output requests retained ihInput ihOutput =>
      exact (append_subset (append_subset ihInput ihOutput) (List.Subset.refl _)).trans
        (List.subset_append_left _ _)

abbrev Signature := Instance → Nat → Option (Port × Port)
abbrev TypeEnv := Nat → Option Port
def TypeEnv.empty : TypeEnv := fun _ => none
def TypeEnv.extend (environment : TypeEnv) (name : Nat) (type : Port) : TypeEnv :=
  fun other => if other = name then some type else environment other

def eraseSignature (signature : Typing.Signature) : Signature :=
  fun effect operation => (signature effect operation).map (fun ports => (eraseType ports.1, eraseType ports.2))
def eraseEnvironment (environment : Typing.TypeEnv) : TypeEnv :=
  fun name => (environment name).map eraseType

inductive Ticket where
  | none
  | bound : Nat → Port → Port → List Instance → List Instance → Ticket
  deriving DecidableEq, Repr

def eraseTicket : Typing.TicketType → Ticket
  | .none => .none
  | .bound binder input answer residual closing =>
      .bound binder (eraseType input) (eraseType answer) residual closing

def InWorld (world : World) (type : Port) : Prop := type.resources ⊆ world
def Covers (signature : Signature) (effect : Instance) (clauses : Clauses) : Prop :=
  ∀ operation input output, signature effect operation = some (input, output) →
    operation ∈ ScopedTyping.clauseKeys clauses

mutual
inductive Typed (signature : Signature) : World → TypeEnv → Ticket → List Instance → Code → Port → Prop where
  | unit : Typed signature world environment ticket allowed .unit .unit
  | boolean : Typed signature world environment ticket allowed (.boolean value) .boolean
  | integer : Typed signature world environment ticket allowed (.integer value) .integer
  | «variable» (known : environment name = some type) (formed : InWorld world type) :
      Typed signature world environment ticket allowed (.variable name) type
  | reference (issued : identity ∈ world) :
      Typed signature world environment ticket allowed (.resourceRef (.activation identity)) (.reference identity)
  | pair : Typed signature world environment ticket allowed left leftType →
      Typed signature world environment ticket allowed right rightType →
      Typed signature world environment ticket allowed (.pair left right) (.product leftType rightType)
  | lambda : Typed signature world (environment.extend parameter input) .none latent body output →
      InWorld world (.function input output latent) →
      Typed signature world environment ticket allowed (.lambda parameter body) (.function input output latent)
  | app : Typed signature world environment ticket allowed function (.function input output latent) →
      Typed signature world environment ticket allowed argument input → latent ⊆ allowed →
      Typed signature world environment ticket allowed (.app function argument) output
  | bind : Typed signature world environment ticket allowed initializer input →
      Typed signature world (environment.extend parameter input) ticket allowed suffix output →
      Typed signature world environment ticket allowed (.bind parameter initializer suffix) output
  | branch : Typed signature world environment ticket allowed condition .boolean →
      Typed signature world environment ticket allowed yes type → Typed signature world environment ticket allowed no type →
      Typed signature world environment ticket allowed (.branch condition yes no) type
  | perform : signature effect operation = some (input, output) → effect ∈ allowed →
      Typed signature world environment ticket allowed operand input → InWorld world output →
      Typed signature world environment ticket allowed (.perform (freezeEffect effect) operation operand) output
  | handle : Typed signature world environment ticket (effect :: residual) body answer →
      ClausesTyped signature world environment effect answer residual clauses → Covers signature effect clauses →
      (ScopedTyping.clauseKeys clauses).Nodup → residual ⊆ allowed →
      Typed signature world environment ticket allowed (.handle (freezeEffect effect) body clauses) answer
  | resume : Typed signature world environment (.bound binder input answer residual closing) allowed operand input →
      residual ⊆ allowed → InWorld world answer →
      Typed signature world environment (.bound binder input answer residual closing) allowed (.resume binder operand) answer
  | discard : closing ⊆ allowed →
      Typed signature world environment (.bound binder input answer residual closing) allowed (.discard binder) .unit
  | resource (initializerChecked : Typed signature world environment ticket allowed initializer .integer)
      (bodyChecked : ∀ identity, identity ∉ world →
        Typed signature (world ++ [identity]) environment ticket (.cell identity :: residual)
          (body.instantiate (Environment.empty.bind binder identity)) answer)
      (resultBound : InWorld world answer) (effectsBound : residual.flatMap Instance.resources ⊆ world)
      (effects : residual ⊆ allowed) :
      Typed signature world environment ticket allowed (.resource binder initializer body) answer
  | cleanup : Typed signature world environment ticket allowed action (.function .unit .unit latent) →
      Typed signature world environment ticket allowed body answer → latent ⊆ allowed →
      Typed signature world environment ticket allowed (.cleanup action body) answer

inductive ClausesTyped (signature : Signature) : World → TypeEnv → Instance → Port → List Instance → Clauses → Prop where
  | nil : ClausesTyped signature world environment effect answer residual .nil
  | cons : signature effect operation = some (input, output) →
      Typed signature world (environment.extend parameter input) (.bound binder output answer residual residual) residual body answer →
      ClausesTyped signature world environment effect answer residual rest →
      ClausesTyped signature world environment effect answer residual (.cons operation parameter binder body rest)
end

theorem erase_world (formed : ScopedTyping.InWorld world type) : InWorld world (eraseType type) :=
  (erasure_preserves_declared_resources type).trans formed

@[simp] theorem erase_environment_extend (environment : Typing.TypeEnv) (name : Nat) (type : Ty) :
    eraseEnvironment (environment.extend name type) = (eraseEnvironment environment).extend name (eraseType type) := by
  funext other
  by_cases same : other = name <;> simp [eraseEnvironment, Typing.TypeEnv.extend, TypeEnv.extend, same]

theorem erase_lookup (known : signature effect operation = some (input, output)) :
    eraseSignature signature effect operation = some (eraseType input, eraseType output) := by
  simp [eraseSignature, known]

theorem erase_coverage (covered : ScopedTyping.Covers signature effect clauses) :
    Covers (eraseSignature signature) effect clauses := by
  intro operation input output known
  cases found : signature effect operation with
  | none => simp [eraseSignature, found] at known
  | some ports => exact covered operation ports.1 ports.2 found

/-- All existing annotated derivations retain their declared port typing.
    This theorem transports neither support admission nor runtime annotations. -/
theorem typed_erasure (typed : ScopedTyping.Typed signature world environment ticket allowed code type) :
    Typed (eraseSignature signature) world (eraseEnvironment environment) (eraseTicket ticket) allowed code (eraseType type) := by
  induction typed using ScopedTyping.Typed.rec
    (motive_2 := fun world environment effect answer residual clauses _ =>
      ClausesTyped (eraseSignature signature) world (eraseEnvironment environment) effect (eraseType answer) residual clauses) with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | «variable» known formed => exact .variable (by simp [eraseEnvironment, known]) (erase_world formed)
  | reference issued => exact .reference issued
  | pair _ _ left right => exact .pair left right
  | lambda _ retained formed body => exact .lambda (by simpa [eraseTicket] using body) (erase_world formed)
  | app _ _ effects function argument => exact .app function argument effects
  | bind _ _ initializer suffix => exact .bind initializer (by simpa using suffix)
  | branch _ _ _ condition yes no => exact .branch condition yes no
  | perform known available _ formed operand => exact .perform (erase_lookup known) available operand (erase_world formed)
  | handle _ _ coverage unique effects body clauses => exact .handle body clauses (erase_coverage coverage) unique effects
  | resume _ effects formed operand => exact .resume operand effects (erase_world formed)
  | discard effects => exact .discard effects
  | resource _ _ formed effectsBound effects initializer body =>
      exact .resource initializer body (erase_world formed) effectsBound effects
  | cleanup _ _ effects action body => exact .cleanup action body effects
  | nil => exact .nil
  | cons known _ _ body rest => exact .cons (erase_lookup known) (by simpa [eraseTicket] using body) rest

theorem typed_result_in_world (typed : Typed signature world environment ticket allowed code type) : InWorld world type := by
  induction typed using Typed.rec (motive_2 := fun _ _ _ _ _ _ _ => True) with
  | unit | boolean | integer | discard => exact List.nil_subset _
  | «variable» _ formed | lambda _ formed _ | perform _ _ _ formed _ | resume _ _ formed _ => exact formed
  | reference issued => intro key member; obtain rfl := List.mem_singleton.mp member; exact issued
  | pair _ _ left right =>
      intro identity member
      exact (List.mem_append.mp member).elim (fun here => left here) (fun there => right there)
  | app _ _ _ function argument =>
      intro key member
      exact function (List.mem_append_left _ (List.mem_append_right _ member))
  | bind _ _ initializer suffix => exact suffix
  | branch _ _ _ condition yes no => exact yes
  | handle _ _ _ _ _ body clauses => exact body
  | resource _ _ formed _ _ initializer body => exact formed
  | cleanup _ _ _ action body => exact body
  | nil | cons => trivial

namespace Support
open Syntax (Dependency resourceDependencies mem_resourceDependencies mem_without)

/-- Support belongs to lexical values, not their declaration types. -/
abbrev Env := Nat → List Nat
def empty : Env := fun _ => []
def extend (environment : Env) (name : Nat) (resources : List Nat) : Env :=
  fun other => if other = name then resources else environment other

def evaluate (environment : Env) (dependencies : List Dependency) : List Nat :=
  dependencies.flatMap fun dependency => match dependency with
    | .resource identity => [identity]
    | .variable name => environment name
    | .ticket _ => []

theorem empty_evaluation (dependencies : List Dependency) :
    evaluate empty dependencies = resourceDependencies dependencies := by
  induction dependencies with
  | nil => rfl
  | cons dependency rest ih => cases dependency <;> simpa [evaluate, empty, resourceDependencies] using ih

theorem evaluation_congr {dependencies : List Dependency}
    (agree : ∀ name, Dependency.variable name ∈ dependencies → source name = destination name) :
    evaluate source dependencies = evaluate destination dependencies := by
  induction dependencies with
  | nil => rfl
  | cons dependency rest ih =>
      have tailEq := ih (fun name member => agree name (List.mem_cons_of_mem _ member))
      have headEq : evaluate source [dependency] = evaluate destination [dependency] := by
        cases dependency with
        | resource | ticket => rfl
        | «variable» name => simp [evaluate, agree name List.mem_cons_self]
      simpa only [evaluate, List.flatMap_cons, List.flatMap_nil, List.append_nil] using
        (congrArg (fun xs => xs ++ evaluate source rest) headEq).trans
          (congrArg (fun xs => evaluate destination [dependency] ++ xs) tailEq)

/-- Instantiating an ordinary value transfers its independently bounded support.
    The bound accounts for variable use; an unused parameter adds no support. -/
theorem substitution_support_bound (expression : Code) (name : Nat)
    (closed : ClosedValue value)
    (valueSupport : resourceDependencies value.dependencies ⊆ resources) :
    evaluate environment (expression.subst name value).dependencies ⊆
      evaluate (extend environment name resources) expression.dependencies := by
  by_cases occurs : Dependency.variable name ∈ expression.dependencies
  · intro identity retained
    obtain ⟨dependency, present, inHead⟩ := List.mem_flatMap.mp retained
    rcases List.mem_append.mp (ScopedTyping.substitution_bound_for_closed_value expression name closed present) with original | inserted
    · obtain ⟨old, different⟩ := mem_without.mp original
      apply List.mem_flatMap.mpr
      refine ⟨dependency, old, ?_⟩
      cases dependency with
      | resource | ticket => exact inHead
      | «variable» other =>
          have distinct : other ≠ name := by simpa using different
          simpa only [extend, if_neg distinct] using inHead
    · cases dependency with
      | «variable» other => exact False.elim (ScopedTyping.closedValue_no_variable closed inserted)
      | ticket binder => exact False.elim (ScopedTyping.closedValue_no_ticket closed inserted)
      | resource resource =>
          have same : identity = resource := by simpa using inHead
          subst identity
          have bound := valueSupport (mem_resourceDependencies.mpr inserted)
          exact List.mem_flatMap.mpr ⟨.variable name, occurs, by simpa [extend] using bound⟩
  · rw [ScopedTyping.subst_absent expression name value occurs]
    have agreement : ∀ other, Dependency.variable other ∈ expression.dependencies →
        environment other = extend environment name resources other := by
      intro other retained
      have different : other ≠ name := by
        intro same
        subst other
        exact occurs retained
      simp [extend, different]
    rw [evaluation_congr agreement]
    exact List.Subset.refl _

/-- Actual handler parameter binding uses the same ordinary substitution rule.
    Input support is not recovered from the declared operation port. -/
theorem parameter_binding_preserves_support {body value : Code}
    (closed : ClosedValue value)
    (valueSupport : resourceDependencies value.dependencies ⊆ resources)
    (bodySupport : evaluate (extend empty parameter resources) body.dependencies ⊆ available) :
    resourceDependencies (body.subst parameter value).dependencies ⊆ available := by
  rw [← empty_evaluation]
  exact (substitution_support_bound body parameter closed valueSupport).trans bodySupport

/-- A returned value cannot retain a resource excluded by its support bound. -/
theorem result_excludes_resource {value : Code}
    (valueSupport : resourceDependencies value.dependencies ⊆ resources)
    (excluded : identity ∉ resources) : identity ∉ resourceDependencies value.dependencies :=
  fun retained => excluded (valueSupport retained)

end Support

namespace Examples
open ScopedSignatureGap.Examples

def callbackPort : Port := .function .unit .integer []
def signature : Signature := fun effect operation =>
  if effect = send ∧ operation = 0 then some (callbackPort, .unit) else none

theorem signature_fixed (identity : Nat) :
    signature send 0 = some (callbackPort, .unit) ∧ callbackPort.resources = [] ∧
      (payload (.activation identity)).dependencies = [.resource identity] := by
  simp [signature, callbackPort, Port.resources, payload, Code.dependencies, Syntax.without]

theorem payload_typed (issued : identity ∈ world) :
    Typed signature world environment ticket allowed (payload (.activation identity)) callbackPort := by
  exact .lambda (.bind (.reference issued) .integer) (List.nil_subset _)

theorem clauses_typed : ClausesTyped signature world environment send .unit residual clauses :=
  .cons (input := callbackPort) (output := .unit) (by simp [signature])
    (.resume .unit (List.Subset.refl _) (List.nil_subset _)) .nil

theorem coverage : Covers signature send clauses := by
  intro operation input output known
  simp only [signature] at known
  split at known
  · rename_i same
    simp [clauses, ScopedTyping.clauseKeys, same.2]
  · cases known

theorem opened_body_typed (issued : identity ∈ world) :
    Typed signature world environment ticket allowed (openedBody identity) .unit := by
  exact .handle (residual := [])
    (.perform (by simp [signature]) (by simp) (payload_typed issued) (List.nil_subset _))
    clauses_typed coverage (by decide) (List.nil_subset _)

/-- One fixed declaration now types every fresh opening of the actual source.
    Its resource support remains a separate, nonempty fact. -/
theorem generative_source_port_typed : Typed signature [] TypeEnv.empty .none [] program .unit := by
  refine .resource (residual := []) .integer ?_ (List.nil_subset _) (List.nil_subset _) (List.nil_subset _)
  intro identity fresh
  rw [body_opening]
  exact opened_body_typed (by simp)

theorem old_typing_is_strictly_more_restrictive :
    Typed signature [] TypeEnv.empty .none [] program .unit ∧
    ∀ oldSignature answer allowed,
      ¬ ScopedTyping.Typed oldSignature [] Typing.TypeEnv.empty .none allowed program answer :=
  ⟨generative_source_port_typed, safe_source_has_no_fixed_signature_typing⟩

/-- Declared port identity is stable; actual callable support varies with the
    opening and must remain visible at the receiver. -/
theorem fresh_payload_same_port_with_actual_support (identity : Nat) :
    Typed signature [identity] TypeEnv.empty .none [] (payload (.activation identity)) callbackPort ∧
    Syntax.resourceDependencies (payload (.activation identity)).dependencies = [identity] := by
  exact ⟨payload_typed (by simp), by simp [payload, Code.dependencies, Syntax.without, Syntax.resourceDependencies]⟩

def outsideProgram : Code := .handle (freezeEffect send)
  (.resource 4 (.integer 41) (.perform (freezeEffect send) 0 (payload (.bound 4)))) clauses

/-- Port checking deliberately does not decide stored-resource escape. -/
theorem outside_source_port_typed : Typed signature [] TypeEnv.empty .none [] outsideProgram .unit := by
  refine .handle (residual := []) (.resource (residual := [send]) .integer ?_
    (List.nil_subset _) ?_ (by simp)) clauses_typed coverage (by decide) (List.nil_subset _)
  · intro identity fresh
    change Typed signature [identity] TypeEnv.empty .none [.cell identity, send]
      (.perform (freezeEffect send) 0 (payload (.activation identity))) .unit
    exact .perform (by simp [signature]) (by simp) (payload_typed (by simp)) (List.nil_subset _)
  · simp [send, Instance.resources]

/-- The original capture-support check rejects the outside ordering even though
    its port derivation succeeds. The handler's unused parameter changes neither
    its recipient position nor the operand boundary requirement. -/
theorem outside_capture_rejected :
    ¬ ScopedExecution.AccessChecks
      ⟨.perform (freezeEffect send) 0 (payload (.activation 0)), .none,
        .push (.cell 0 41 .none .unit) (.push (.handler handler) .nil)⟩ [] := by
  intro checked
  have cut : ScopedExecution.HandlerCut send
      (.push (.cell 0 41 .none .unit) (.push (.handler handler) .nil))
      (.push (.cell 0 41 .none .unit) (.push (.handler handler) .nil)) .nil handler :=
    .push _ _ _ _ _ (by simp [ScopedExecution.ExecFrame.erase, Frame.target, send])
      (.hit handler .nil rfl)
  have impossible := checked.capture send 0 (payload (.activation 0)) .none _ _ _ handler
    rfl cut payload_closed (opened_payload_retains 0)
  simp [ScopedExecution.Stack.erase, Control.visible] at impossible

/-- Substitution may return the entire callback through a handler parameter;
    its retained cell survives despite the resource-free declared arrow. -/
theorem handler_parameter_retains_actual_support :
    Syntax.resourceDependencies
      ((Code.variable 5).subst 5 (payload (.activation 0))).dependencies = [0] ∧
    callbackPort.resources = [] := by
  simp [Code.subst, payload, Code.dependencies, Syntax.without, Syntax.resourceDependencies,
    callbackPort, Port.resources]

end Examples
end Ash.OneShot.ScopedPorts

#print axioms Ash.OneShot.ScopedPorts.erasure_preserves_declared_resources
#print axioms Ash.OneShot.ScopedPorts.erase_world
#print axioms Ash.OneShot.ScopedPorts.erase_environment_extend
#print axioms Ash.OneShot.ScopedPorts.erase_lookup
#print axioms Ash.OneShot.ScopedPorts.erase_coverage
#print axioms Ash.OneShot.ScopedPorts.typed_erasure
#print axioms Ash.OneShot.ScopedPorts.typed_result_in_world
#print axioms Ash.OneShot.ScopedPorts.Examples.signature_fixed
#print axioms Ash.OneShot.ScopedPorts.Examples.payload_typed
#print axioms Ash.OneShot.ScopedPorts.Examples.clauses_typed
#print axioms Ash.OneShot.ScopedPorts.Examples.coverage
#print axioms Ash.OneShot.ScopedPorts.Examples.opened_body_typed
#print axioms Ash.OneShot.ScopedPorts.Examples.generative_source_port_typed
#print axioms Ash.OneShot.ScopedPorts.Examples.old_typing_is_strictly_more_restrictive
#print axioms Ash.OneShot.ScopedPorts.Support.empty_evaluation
#print axioms Ash.OneShot.ScopedPorts.Support.evaluation_congr
#print axioms Ash.OneShot.ScopedPorts.Support.substitution_support_bound
#print axioms Ash.OneShot.ScopedPorts.Support.parameter_binding_preserves_support
#print axioms Ash.OneShot.ScopedPorts.Support.result_excludes_resource
#print axioms Ash.OneShot.ScopedPorts.Examples.fresh_payload_same_port_with_actual_support
#print axioms Ash.OneShot.ScopedPorts.Examples.outside_source_port_typed
#print axioms Ash.OneShot.ScopedPorts.Examples.outside_capture_rejected
#print axioms Ash.OneShot.ScopedPorts.Examples.handler_parameter_retains_actual_support
