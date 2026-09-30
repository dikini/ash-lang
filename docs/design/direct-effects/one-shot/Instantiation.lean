import PreparedExecution

/-!
Lexical resource instantiation for the existing monomorphic metadata fragment.
Source binders and runtime activation atoms occupy distinct namespaces. The
judgments realize exact instances, port types, latent rows, and retained support;
they do not introduce a second computation calculus. Integrating this layer
with source expression evaluation remains a separate proof obligation.
-/

namespace Ash.OneShot.Instantiation
open Syntax Execution Typing Joint Progress PreparedExecution

/-- Activation atoms are internal realized metadata, not source authority. -/
inductive ResourceName where
  | bound : Nat → ResourceName
  | activation : Nat → ResourceName
  deriving DecidableEq, Repr

abbrev Environment := Nat → Option Nat

def Environment.empty : Environment := fun _ => none

def Environment.bind (environment : Environment) (name activation : Nat) : Environment :=
  fun other => if other = name then some activation else environment other

inductive NameRealizes (environment : Environment) : ResourceName → Nat → Prop where
  | bound (known : environment name = some activation) : NameRealizes environment (.bound name) activation
  | activation : NameRealizes environment (.activation activation) activation

inductive Argument where
  | nominal : Nat → Argument
  | resource : ResourceName → Argument
  | apply : Argument → Argument → Argument
  deriving DecidableEq, Repr

inductive Effect where
  | user : Nat → List Argument → Effect
  | cell : ResourceName → Effect
  deriving DecidableEq, Repr

inductive ValueType where
  | unit | boolean | integer
  | product : ValueType → ValueType → ValueType
  | reference : ResourceName → ValueType
  | function : ValueType → ValueType → List Effect → List ResourceName → ValueType
  deriving DecidableEq, Repr

inductive ListRealizes (relation : α → β → Prop) : List α → List β → Prop where
  | nil : ListRealizes relation [] []
  | cons (checked : relation a b) (rest : ListRealizes relation as bs) :
      ListRealizes relation (a :: as) (b :: bs)

inductive ArgumentRealizes (environment : Environment) : Argument → TypeArgument → Prop where
  | nominal : ArgumentRealizes environment (.nominal identity) (.nominal identity)
  | resource (name : NameRealizes environment source activation) :
      ArgumentRealizes environment (.resource source) (.resource activation)
  | apply (headChecked : ArgumentRealizes environment sourceHead head)
      (argumentChecked : ArgumentRealizes environment sourceArgument argument) :
      ArgumentRealizes environment (.apply sourceHead sourceArgument) (.apply head argument)

inductive EffectRealizes (environment : Environment) : Effect → Instance → Prop where
  | user (argumentsChecked : ListRealizes (ArgumentRealizes environment) sourceArguments arguments) :
      EffectRealizes environment (.user family sourceArguments) (.user family arguments)
  | cell (name : NameRealizes environment source activation) :
      EffectRealizes environment (.cell source) (.cell activation)

inductive TypeRealizes (environment : Environment) : ValueType → Ty → Prop where
  | unit : TypeRealizes environment .unit .unit
  | boolean : TypeRealizes environment .boolean .boolean
  | integer : TypeRealizes environment .integer .integer
  | product (leftChecked : TypeRealizes environment sourceLeft left) (rightChecked : TypeRealizes environment sourceRight right) :
      TypeRealizes environment (.product sourceLeft sourceRight) (.product left right)
  | reference (name : NameRealizes environment source activation) :
      TypeRealizes environment (.reference source) (.reference activation)
  | function (inputChecked : TypeRealizes environment sourceInput input) (outputChecked : TypeRealizes environment sourceOutput output)
      (requestsChecked : ListRealizes (EffectRealizes environment) sourceRequests requests)
      (retainedChecked : ListRealizes (NameRealizes environment) sourceRetained retained) :
      TypeRealizes environment (.function sourceInput sourceOutput sourceRequests sourceRetained)
        (.function input output requests retained)

variable {environment : Environment}

/-- Rebinding changes only one source-name lookup. Previously realized atoms
    require no environment lookup and remain fixed in all later contexts. -/
theorem acquired_name_realizes : NameRealizes (environment.bind name activation) (.bound name) activation :=
  .bound (by simp [Environment.bind])

theorem other_name_retained (known : environment other = some previous) (different : other ≠ name) :
    NameRealizes (environment.bind name activation) (.bound other) previous :=
  .bound (by simp [Environment.bind, different, known])

theorem activation_is_never_rebound (environment : Environment) :
    NameRealizes (environment.bind name fresh) (.activation previous) previous := .activation

theorem name_realization_unique (first : NameRealizes environment source a)
    (second : NameRealizes environment source b) : a = b := by
  cases first with
  | activation => cases second; rfl
  | bound known => cases second with
      | bound other => exact Option.some.inj (known.symm.trans other)

theorem argument_realization_unique (first : ArgumentRealizes environment source a)
    (second : ArgumentRealizes environment source b) : a = b := by
  induction first generalizing b with
  | nominal => cases second; rfl
  | resource name => cases second with
      | resource other => exact congrArg TypeArgument.resource (name_realization_unique name other)
  | apply head argument ihHead ihArgument => cases second with
      | apply otherHead otherArgument => rw [ihHead otherHead, ihArgument otherArgument]

theorem list_realization_unique {relation : α → β → Prop}
    (unique : ∀ source a b, relation source a → relation source b → a = b)
    (first : ListRealizes relation source a) (second : ListRealizes relation source b) : a = b := by
  induction first generalizing b with
  | nil => cases second; rfl
  | cons head rest ih => cases second with
      | cons otherHead otherRest => rw [unique _ _ _ head otherHead, ih otherRest]

theorem effect_realization_unique (first : EffectRealizes environment source a)
    (second : EffectRealizes environment source b) : a = b := by
  cases first with
  | user arguments => cases second with
      | user other => exact congrArg (Instance.user _) (list_realization_unique
          (relation := ArgumentRealizes environment)
          (fun _ _ _ first second => argument_realization_unique first second) arguments other)
  | cell name => cases second with
      | cell other => exact congrArg Instance.cell (name_realization_unique name other)

theorem type_realization_unique (first : TypeRealizes environment source a)
    (second : TypeRealizes environment source b) : a = b := by
  induction first generalizing b with
  | unit => cases second; rfl
  | boolean => cases second; rfl
  | integer => cases second; rfl
  | reference name => cases second with
      | reference other => exact congrArg Ty.reference (name_realization_unique name other)
  | product left right ihLeft ihRight => cases second with
      | product otherLeft otherRight => rw [ihLeft otherLeft, ihRight otherRight]
  | function input output requests retained ihInput ihOutput => cases second with
      | function otherInput otherOutput otherRequests otherRetained =>
          rw [ihInput otherInput, ihOutput otherOutput,
            list_realization_unique (relation := EffectRealizes environment)
              (fun _ _ _ first second => effect_realization_unique first second) requests otherRequests,
            list_realization_unique (relation := NameRealizes environment)
              (fun _ _ _ first second => name_realization_unique first second) retained otherRetained]

def freezeArgument : TypeArgument → Argument
  | .nominal identity => .nominal identity
  | .resource activation => .resource (.activation activation)
  | .apply head argument => .apply (freezeArgument head) (freezeArgument argument)

def freezeEffect : Instance → Effect
  | .user family arguments => .user family (arguments.map freezeArgument)
  | .cell activation => .cell (.activation activation)

def freezeType : Ty → ValueType
  | .unit => .unit
  | .boolean => .boolean
  | .integer => .integer
  | .product left right => .product (freezeType left) (freezeType right)
  | .reference activation => .reference (.activation activation)
  | .function input output requests retained =>
      .function (freezeType input) (freezeType output) (requests.map freezeEffect) (retained.map ResourceName.activation)

theorem list_freeze_realizes {relation : α → β → Prop} {freeze : β → α}
    (realizes : ∀ value, relation (freeze value) value) (values : List β) :
    ListRealizes relation (values.map freeze) values := by
  induction values with
  | nil => exact .nil
  | cons value rest ih => exact .cons (realizes value) ih

theorem frozen_argument_realizes (environment : Environment) (argument : TypeArgument) :
    ArgumentRealizes environment (freezeArgument argument) argument := by
  induction argument with
  | nominal => exact .nominal
  | resource => exact .resource .activation
  | apply head argument ihHead ihArgument => exact .apply ihHead ihArgument

theorem frozen_effect_realizes (environment : Environment) (effect : Instance) :
    EffectRealizes environment (freezeEffect effect) effect := by
  cases effect with
  | user family arguments => exact .user (list_freeze_realizes (frozen_argument_realizes environment) arguments)
  | cell => exact .cell .activation

/-- Already realized metadata, including nested port types, latent rows, and
    retained support, is invariant under any later lexical environment. -/
theorem frozen_type_realizes (environment : Environment) (type : Ty) :
    TypeRealizes environment (freezeType type) type := by
  induction type with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | product left right ihLeft ihRight => exact .product ihLeft ihRight
  | reference => exact .reference .activation
  | function input output requests retained ihInput ihOutput =>
      exact .function ihInput ihOutput (list_freeze_realizes (frozen_effect_realizes environment) requests)
        (list_freeze_realizes (fun _ => NameRealizes.activation) retained)

theorem frozen_effect_cannot_change
    (realized : EffectRealizes environment (freezeEffect original) actual) : actual = original :=
  effect_realization_unique realized (frozen_effect_realizes environment original)

theorem frozen_type_cannot_change
    (realized : TypeRealizes environment (freezeType original) actual) : actual = original :=
  type_realization_unique realized (frozen_type_realizes environment original)

def Argument.resources : Argument → List ResourceName
  | .nominal _ => []
  | .resource name => [name]
  | .apply head argument => head.resources ++ argument.resources

def Effect.resources : Effect → List ResourceName
  | .user _ arguments => arguments.flatMap Argument.resources
  | .cell name => [name]

def ValueType.resources : ValueType → List ResourceName
  | .unit | .boolean | .integer => []
  | .product left right => left.resources ++ right.resources
  | .reference name => [name]
  | .function input output requests retained =>
      input.resources ++ output.resources ++ requests.flatMap Effect.resources ++ retained

/-- Availability checks only source-name lookup. Activation atoms need no
    lookup; this judgment grants neither live access nor ownership. -/
def NameBound (environment : Environment) : ResourceName → Prop
  | .bound name => ∃ activation, environment name = some activation
  | .activation _ => True

def NamesBound (environment : Environment) (names : List ResourceName) : Prop :=
  ∀ name, name ∈ names → NameBound environment name

theorem names_bound_append (checked : NamesBound environment (left ++ right)) :
    NamesBound environment left ∧ NamesBound environment right :=
  ⟨fun name member => checked name (List.mem_append_left _ member),
   fun name member => checked name (List.mem_append_right _ member)⟩

theorem name_realization_exists (checked : NameBound environment source) :
    ∃ target, NameRealizes environment source target := by
  cases source with
  | bound name => obtain ⟨target, known⟩ := checked; exact ⟨target, .bound known⟩
  | activation target => exact ⟨target, .activation⟩

theorem list_realization_exists {relation : α → β → Prop} (source : List α)
    (checked : ∀ value, value ∈ source → ∃ target, relation value target) :
    ∃ target, ListRealizes relation source target := by
  induction source with
  | nil => exact ⟨[], .nil⟩
  | cons value rest ih =>
      obtain ⟨head, headChecked⟩ := checked value List.mem_cons_self
      obtain ⟨tail, tailChecked⟩ := ih (fun value member => checked value (List.mem_cons_of_mem _ member))
      exact ⟨head :: tail, .cons headChecked tailChecked⟩

theorem argument_realization_exists (source : Argument)
    (checked : NamesBound environment source.resources) :
    ∃ target, ArgumentRealizes environment source target := by
  induction source with
  | nominal identity => exact ⟨.nominal identity, .nominal⟩
  | resource name =>
      obtain ⟨target, realized⟩ := name_realization_exists (checked name List.mem_cons_self)
      exact ⟨.resource target, .resource realized⟩
  | apply head argument ihHead ihArgument =>
      obtain ⟨headBound, argumentBound⟩ := names_bound_append checked
      obtain ⟨headTarget, headChecked⟩ := ihHead headBound
      obtain ⟨argumentTarget, argumentChecked⟩ := ihArgument argumentBound
      exact ⟨.apply headTarget argumentTarget, .apply headChecked argumentChecked⟩

theorem effect_realization_exists (source : Effect)
    (checked : NamesBound environment source.resources) :
    ∃ target, EffectRealizes environment source target := by
  cases source with
  | cell name =>
      obtain ⟨target, realized⟩ := name_realization_exists (checked name List.mem_cons_self)
      exact ⟨.cell target, .cell realized⟩
  | user family arguments =>
      obtain ⟨targets, realized⟩ := list_realization_exists (relation := ArgumentRealizes environment)
        arguments (fun argument member => argument_realization_exists argument
          (fun name present => checked name (List.mem_flatMap.mpr ⟨argument, member, present⟩)))
      exact ⟨.user family targets, .user realized⟩

/-- Metadata realization exists from finite lexical lookup obligations. In
    particular, determinism is not conditional on an uninhabited relation. -/
theorem type_realization_exists (source : ValueType)
    (checked : NamesBound environment source.resources) :
    ∃ target, TypeRealizes environment source target := by
  induction source with
  | unit => exact ⟨.unit, .unit⟩
  | boolean => exact ⟨.boolean, .boolean⟩
  | integer => exact ⟨.integer, .integer⟩
  | reference name =>
      obtain ⟨target, realized⟩ := name_realization_exists (checked name List.mem_cons_self)
      exact ⟨.reference target, .reference realized⟩
  | product left right ihLeft ihRight =>
      obtain ⟨leftBound, rightBound⟩ := names_bound_append checked
      obtain ⟨leftTarget, leftChecked⟩ := ihLeft leftBound
      obtain ⟨rightTarget, rightChecked⟩ := ihRight rightBound
      exact ⟨.product leftTarget rightTarget, .product leftChecked rightChecked⟩
  | function input output requests retained ihInput ihOutput =>
      obtain ⟨portsRequestsBound, retainedBound⟩ := names_bound_append checked
      obtain ⟨portsBound, requestsBound⟩ := names_bound_append portsRequestsBound
      obtain ⟨inputBound, outputBound⟩ := names_bound_append portsBound
      obtain ⟨inputTarget, inputChecked⟩ := ihInput inputBound
      obtain ⟨outputTarget, outputChecked⟩ := ihOutput outputBound
      obtain ⟨requestTargets, requestsChecked⟩ := list_realization_exists (relation := EffectRealizes environment)
        requests (fun request member => effect_realization_exists request
          (fun name present => requestsBound name (List.mem_flatMap.mpr ⟨request, member, present⟩)))
      obtain ⟨retainedTargets, retainedChecked⟩ := list_realization_exists (relation := NameRealizes environment)
        retained (fun name member => name_realization_exists (retainedBound name member))
      exact ⟨.function inputTarget outputTarget requestTargets retainedTargets,
        .function inputChecked outputChecked requestsChecked retainedChecked⟩

theorem list_append_realizes (left : ListRealizes relation a b) (right : ListRealizes relation c d) :
    ListRealizes relation (a ++ c) (b ++ d) := by
  induction left with
  | nil => exact right
  | cons head rest ih => exact .cons head ih

theorem list_flatMap_realizes {relation : α → β → Prop} {leaves : γ → δ → Prop}
    {sourceLeaves : α → List γ} {targetLeaves : β → List δ}
    (project : ∀ a b, relation a b → ListRealizes leaves (sourceLeaves a) (targetLeaves b))
    (checked : ListRealizes relation source target) :
    ListRealizes leaves (source.flatMap sourceLeaves) (target.flatMap targetLeaves) := by
  induction checked with
  | nil => exact .nil
  | cons head rest ih => exact list_append_realizes (project _ _ head) ih

theorem argument_resources_realize (checked : ArgumentRealizes environment source target) :
    ListRealizes (NameRealizes environment) source.resources target.resources := by
  induction checked with
  | nominal => exact .nil
  | resource name => exact .cons name .nil
  | apply head argument ihHead ihArgument => exact list_append_realizes ihHead ihArgument

theorem effect_resources_realize (checked : EffectRealizes environment source target) :
    ListRealizes (NameRealizes environment) source.resources target.resources := by
  cases checked with
  | user arguments =>
      exact list_flatMap_realizes
        (relation := ArgumentRealizes environment) (fun _ _ realized => argument_resources_realize realized) arguments
  | cell name => exact .cons name .nil

/-- Resource support is transported through all metadata positions, including
    nested argument applications, function ports, latent rows, and retention. -/
theorem type_resources_realize (checked : TypeRealizes environment source target) :
    ListRealizes (NameRealizes environment) source.resources target.resources := by
  induction checked with
  | unit | boolean | integer => exact .nil
  | reference name => exact .cons name .nil
  | product left right ihLeft ihRight => exact list_append_realizes ihLeft ihRight
  | function input output requests retained ihInput ihOutput =>
      exact list_append_realizes (list_append_realizes (list_append_realizes ihInput ihOutput)
        (list_flatMap_realizes (relation := EffectRealizes environment)
          (fun _ _ realized => effect_resources_realize realized) requests)) retained

theorem realized_member_has_origin (checked : ListRealizes relation source target)
    (present : value ∈ target) : ∃ name, name ∈ source ∧ relation name value := by
  induction checked with
  | nil => cases present
  | cons head rest ih =>
      rcases List.mem_cons.mp present with same | later
      · subst value
        exact ⟨_, List.mem_cons_self, head⟩
      · obtain ⟨name, member, related⟩ := ih later
        exact ⟨name, List.mem_cons_of_mem _ member, related⟩

theorem realized_type_support
    (checked : TypeRealizes environment source target)
    (provided : ∀ name, name ∈ source.resources → ∀ activation,
      NameRealizes environment name activation → activation ∈ available) :
    target.resources ⊆ available := by
  intro activation present
  obtain ⟨name, member, realized⟩ := realized_member_has_origin (type_resources_realize checked) present
  exact provided name member activation realized

/-- This records historical issuance, not live access or owning authority. -/
def EnvironmentHistory (environment : Environment) (issued : List Owner) : Prop :=
  ∀ name activation, environment name = some activation → Owner.resource activation ∈ issued

structure PreparedActivation (issued : List Owner) where
  identity : Nat
  fresh : Owner.resource identity ∉ issued

def prepareActivation (issued : List Owner) : PreparedActivation issued :=
  ⟨aboveOwners issued, fun present => (Nat.lt_irrefl _) (owner_number_below present)⟩

def PreparedActivation.bodyEnvironment (prepared : PreparedActivation issued)
    (environment : Environment) (name : Nat) : Environment := environment.bind name prepared.identity

theorem prepared_activation_fresh_history (prepared : PreparedActivation issued) (unique : issued.Nodup) :
    (issued ++ [Owner.resource prepared.identity]).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨unique, by simp, ?_⟩
  intro old member new singleton same
  simp only [List.mem_singleton] at singleton
  subst new
  subst old
  exact prepared.fresh member

theorem acquisition_preserves_environment_history (prepared : PreparedActivation issued)
    (history : EnvironmentHistory environment issued) :
    EnvironmentHistory (prepared.bodyEnvironment environment name) (issued ++ [.resource prepared.identity]) := by
  intro other activation known
  by_cases same : other = name
  · subst other
    simp [PreparedActivation.bodyEnvironment, Environment.bind] at known
    subst activation
    exact List.mem_append_right _ (by simp)
  · have previous : environment other = some activation := by
      simpa [PreparedActivation.bodyEnvironment, Environment.bind, same] using known
    exact List.mem_append_left _ (history other activation previous)

theorem acquired_activation_differs_from_earlier_bindings (prepared : PreparedActivation issued)
    (history : EnvironmentHistory environment issued) (known : environment name = some previous) :
    prepared.identity ≠ previous := by
  intro same
  apply prepared.fresh
  simpa only [same] using history name previous known

/-- Once a source body has been realized, the existing runtime entry owns the
    prepared activation and preserves the ledger. This does not itself realize
    source code or replace the missing expression-instantiation theorem. -/
theorem prepared_cell_entry_preserves_ledger (prepared : PreparedActivation issued)
    (ledger : Ledger (RunState.erase ⟨⟨.resource prepared.identity (.integer payload) body, scope, tail⟩,
      issued, completed⟩)) :
    Ledger (RunState.erase ⟨⟨body, scope, .push (.cell prepared.identity payload scope answer) tail⟩,
      issued ++ [.resource prepared.identity], completed⟩) := by
  exact run_step_preserves_ledger
    (.event _ _ [.resource prepared.identity] [] (.enterCell prepared.identity payload body scope answer tail)
      (prepared_activation_fresh_history prepared ledger.2)) ledger

namespace Examples

def first : PreparedActivation [] := prepareActivation []
def outer : Environment := first.bodyEnvironment .empty 4
def second : PreparedActivation [.resource first.identity] := prepareActivation [.resource first.identity]
def inner : Environment := second.bodyEnvironment outer 4

def sourceEffect : Effect := .user 9 [.apply (.nominal 3) (.resource (.bound 4))]
def oldEffect : Instance := .user 9 [.apply (.nominal 3) (.resource first.identity)]
def newEffect : Instance := .user 9 [.apply (.nominal 3) (.resource second.identity)]

theorem repeated_site_gets_distinct_activations : first.identity = 0 ∧ second.identity = 1 := ⟨rfl, rfl⟩

theorem outer_effect_realized : EffectRealizes outer sourceEffect oldEffect :=
  .user (.cons (.apply .nominal (.resource (.bound rfl))) .nil)

theorem inner_effect_realized : EffectRealizes inner sourceEffect newEffect :=
  .user (.cons (.apply .nominal (.resource (.bound rfl))) .nil)

theorem captured_effect_keeps_outer_activation :
    EffectRealizes inner (freezeEffect oldEffect) oldEffect := frozen_effect_realizes _ _

def sourceType : ValueType := .function (.reference (.bound 4)) (.product .unit (.reference (.bound 4)))
  [.cell (.bound 4), sourceEffect] [.bound 4]
def oldType : Ty := .function (.reference first.identity) (.product .unit (.reference first.identity))
  [.cell first.identity, oldEffect] [first.identity]

theorem outer_type_realized : TypeRealizes outer sourceType oldType :=
  .function (.reference (.bound rfl)) (.product .unit (.reference (.bound rfl)))
    (.cons (.cell (.bound rfl)) (.cons outer_effect_realized .nil)) (.cons (.bound rfl) .nil)

theorem captured_type_keeps_all_outer_metadata : TypeRealizes inner (freezeType oldType) oldType :=
  frozen_type_realizes _ _

theorem caller_environment_would_change_request : ¬ EffectRealizes inner sourceEffect oldEffect := by
  intro wrong
  have impossible := effect_realization_unique wrong inner_effect_realized
  cases impossible

/-- Distinct lexical aliases may intentionally resolve to the same exact
    runtime instance. Instantiation must not assume global injectivity. -/
theorem aliases_are_not_distinct_instances :
    Effect.cell (.bound 4) ≠ Effect.cell (.bound 5) ∧
    EffectRealizes ((Environment.empty.bind 4 7).bind 5 7) (.cell (.bound 4)) (.cell 7) ∧
    EffectRealizes ((Environment.empty.bind 4 7).bind 5 7) (.cell (.bound 5)) (.cell 7) :=
  ⟨by decide, .cell (.bound rfl), .cell (.bound rfl)⟩

def handler (activation : Nat) (effect : Instance) : HandlerData :=
  ⟨activation, effect, .cons 0 1 9 (.resume 9 .unit) .nil, .none, .unit, rfl⟩
def oldHandler : HandlerData := handler 10 oldEffect
def newHandler : HandlerData := handler 11 newEffect
def outside : Stack := .push (.cell first.identity 17 .none .unit) .nil
def captured : Stack := .push (.handler newHandler)
  (.push (.cell second.identity 99 .none .unit) (.push (.handler oldHandler) .nil))
def whole : Stack := captured.append outside

/-- A request retaining only old lexical effect metadata skips the newer
    same-source-site interpretation. The operand is unit, with no resource
    handle from which dispatch could infer the activation. -/
theorem old_metadata_selects_outer_handler : HandlerCut oldEffect whole captured outside oldHandler := by
  apply HandlerCut.push
  · decide
  · apply HandlerCut.push
    · decide
    · exact HandlerCut.hit oldHandler outside rfl

theorem metadata_only_request_captures_outer :
    RawStep ⟨.perform oldEffect 0 .unit, .none, whole⟩
      ⟨.resume 9 .unit, .ticket 9 3, .live 3 .unit .unit captured .none outside⟩ [.ticket 3] [] :=
  .capture oldEffect 0 1 9 3 .unit (.resume 9 .unit) .none whole captured outside oldHandler .unit
    old_metadata_selects_outer_handler .hit Execution.Examples.closed_unit
    (by simp [ClosedExcept, Expr.dependencies]) (by simp [ResourceFresh, Expr.dependencies])

end Examples

end Ash.OneShot.Instantiation

#print axioms Ash.OneShot.Instantiation.name_realization_unique
#print axioms Ash.OneShot.Instantiation.effect_realization_unique
#print axioms Ash.OneShot.Instantiation.type_realization_unique
#print axioms Ash.OneShot.Instantiation.effect_realization_exists
#print axioms Ash.OneShot.Instantiation.type_realization_exists
#print axioms Ash.OneShot.Instantiation.frozen_effect_cannot_change
#print axioms Ash.OneShot.Instantiation.frozen_type_cannot_change
#print axioms Ash.OneShot.Instantiation.type_resources_realize
#print axioms Ash.OneShot.Instantiation.realized_type_support
#print axioms Ash.OneShot.Instantiation.acquisition_preserves_environment_history
#print axioms Ash.OneShot.Instantiation.acquired_activation_differs_from_earlier_bindings
#print axioms Ash.OneShot.Instantiation.prepared_cell_entry_preserves_ledger
#print axioms Ash.OneShot.Instantiation.Examples.repeated_site_gets_distinct_activations
#print axioms Ash.OneShot.Instantiation.Examples.captured_type_keeps_all_outer_metadata
#print axioms Ash.OneShot.Instantiation.Examples.caller_environment_would_change_request
#print axioms Ash.OneShot.Instantiation.Examples.aliases_are_not_distinct_instances
#print axioms Ash.OneShot.Instantiation.Examples.metadata_only_request_captures_outer
