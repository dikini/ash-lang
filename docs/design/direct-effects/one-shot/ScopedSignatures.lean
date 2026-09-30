import ScopedUsageExecution

/-!
Executable type instantiation and coherent finite operation signatures for the
monomorphic scoped fragment. Source aliases may realize to one exact instance;
coherence checks that their ports agree. Callable ports may retain resources
outside the instance. This is a typing prerequisite, not source admission or
an expression-machine typing/progress theorem.
-/

namespace Ash.OneShot.Instantiation
open ScopedExpressions

def ValueType.instantiate (environment : Environment) : ValueType → ValueType
  | .unit => .unit
  | .boolean => .boolean
  | .integer => .integer
  | .product left right => .product (left.instantiate environment) (right.instantiate environment)
  | .reference name => .reference (name.instantiate environment)
  | .function input output requests retained =>
      .function (input.instantiate environment) (output.instantiate environment)
        (requests.map (Effect.instantiate environment)) (retained.map (ResourceName.instantiate environment))

theorem list_instantiation_realizes {relation : α → β → Prop} {instantiate : α → γ} {freeze : β → γ}
    (agrees : ∀ source target, relation source target → instantiate source = freeze target)
    (checked : ListRealizes relation source target) : source.map instantiate = target.map freeze := by
  induction checked with
  | nil => rfl
  | cons head rest ih => simp only [List.map_cons, agrees _ _ head, ih]

theorem type_instantiation_realizes (checked : TypeRealizes environment source target) :
    source.instantiate environment = freezeType target := by
  induction checked with
  | unit | boolean | integer => rfl
  | reference name => exact congrArg ValueType.reference (name_instantiation_realizes name)
  | product left right ihLeft ihRight => simp only [ValueType.instantiate, freezeType, ihLeft, ihRight]
  | function input output requests retained ihInput ihOutput =>
      simp only [ValueType.instantiate, freezeType, ihInput, ihOutput]
      rw [list_instantiation_realizes (fun _ _ checked => effect_instantiation_realizes checked) requests,
        list_instantiation_realizes (fun _ _ checked => name_instantiation_realizes checked) retained]

theorem frozen_type_instantiation (type : Ty) (environment : Environment) :
    (freezeType type).instantiate environment = freezeType type :=
  type_instantiation_realizes (frozen_type_realizes environment type)

theorem realized_type_cannot_be_rebound (checked : TypeRealizes first source target) (later : Environment) :
    (source.instantiate first).instantiate later = freezeType target := by
  rw [type_instantiation_realizes checked, frozen_type_instantiation]

/-- Traverse every type resource, including function input/output, latent rows,
    and retained support. No injectivity assumption is made about the environment. -/
theorem type_instantiation_resources (type : ValueType) (environment : Environment) :
    (type.instantiate environment).resources = type.resources.map (ResourceName.instantiate environment) := by
  induction type with
  | unit | boolean | integer | reference => rfl
  | product left right ihLeft ihRight =>
      simp only [ValueType.instantiate, ValueType.resources, ihLeft, ihRight, List.map_append]
  | function input output requests retained ihInput ihOutput =>
      simp only [ValueType.instantiate, ValueType.resources, ihInput, ihOutput, List.map_append]
      congr 2
      induction requests with
      | nil => rfl
      | cons effect rest ih =>
          simp only [List.map_cons, List.flatMap_cons, effect_instantiation_resources, List.map_append, ih]

/-- User declarations cannot replace the fixed builtin cell signatures. -/
structure SourceOperation where
  family : Nat
  arguments : List Argument
  operation : Nat
  input : ValueType
  output : ValueType
  deriving DecidableEq, Repr

structure RuntimeOperation where
  family : Nat
  arguments : List TypeArgument
  operation : Nat
  input : Ty
  output : Ty
  deriving DecidableEq, Repr

def SourceOperation.effect (entry : SourceOperation) : Effect := .user entry.family entry.arguments
def RuntimeOperation.effect (entry : RuntimeOperation) : Instance := .user entry.family entry.arguments
def RuntimeOperation.key (entry : RuntimeOperation) : Instance × Nat := (entry.effect, entry.operation)
def RuntimeOperation.ports (entry : RuntimeOperation) : Ty × Ty := (entry.input, entry.output)
def SourceOperation.resources (entry : SourceOperation) : List ResourceName :=
  entry.effect.resources ++ entry.input.resources ++ entry.output.resources

def SourceOperation.instantiate (environment : Environment) (entry : SourceOperation) : SourceOperation :=
  ⟨entry.family, entry.arguments.map (Argument.instantiate environment), entry.operation,
    entry.input.instantiate environment, entry.output.instantiate environment⟩

def freezeOperation (entry : RuntimeOperation) : SourceOperation :=
  ⟨entry.family, entry.arguments.map freezeArgument, entry.operation, freezeType entry.input, freezeType entry.output⟩

inductive OperationRealizes (environment : Environment) : SourceOperation → RuntimeOperation → Prop where
  | operation (argumentsChecked : ListRealizes (ArgumentRealizes environment) sourceArguments arguments)
      (inputChecked : TypeRealizes environment sourceInput input) (outputChecked : TypeRealizes environment sourceOutput output) :
      OperationRealizes environment ⟨family, sourceArguments, operation, sourceInput, sourceOutput⟩
        ⟨family, arguments, operation, input, output⟩

theorem operation_realization_unique (first : OperationRealizes environment source a)
    (second : OperationRealizes environment source b) : a = b := by
  cases first with
  | operation arguments input output => cases second with
      | operation otherArguments otherInput otherOutput =>
          rw [list_realization_unique (relation := ArgumentRealizes environment) (fun _ _ _ a b => argument_realization_unique a b) arguments otherArguments,
            type_realization_unique input otherInput, type_realization_unique output otherOutput]

theorem operation_instantiation_realizes (checked : OperationRealizes environment source target) :
    source.instantiate environment = freezeOperation target := by
  cases checked with
  | operation arguments input output =>
      simp only [SourceOperation.instantiate, freezeOperation]
      rw [list_instantiation_realizes (fun _ _ h => argument_instantiation_realizes h) arguments,
        type_instantiation_realizes input, type_instantiation_realizes output]

theorem frozen_operation_realizes (entry : RuntimeOperation) (environment : Environment) :
    OperationRealizes environment (freezeOperation entry) entry := by
  cases entry
  exact .operation (list_freeze_realizes (frozen_argument_realizes environment) _)
    (frozen_type_realizes environment _) (frozen_type_realizes environment _)

theorem realized_operation_cannot_be_rebound (checked : OperationRealizes first source target) (later : Environment) :
    (source.instantiate first).instantiate later = freezeOperation target := by
  rw [operation_instantiation_realizes checked]
  exact operation_instantiation_realizes (frozen_operation_realizes target later)

theorem operation_realization_exists (entry : SourceOperation)
    (available : NamesBound environment entry.resources) : ∃ target, OperationRealizes environment entry target := by
  obtain ⟨effectAndInput, outputNames⟩ := names_bound_append available
  obtain ⟨effectNames, inputNames⟩ := names_bound_append effectAndInput
  obtain ⟨effect, effectChecked⟩ := effect_realization_exists entry.effect effectNames
  obtain ⟨input, inputChecked⟩ := type_realization_exists entry.input inputNames
  obtain ⟨output, outputChecked⟩ := type_realization_exists entry.output outputNames
  cases entry with
  | mk family arguments operation sourceInput sourceOutput =>
      cases effectChecked with
      | user argumentsChecked => exact ⟨_, .operation argumentsChecked inputChecked outputChecked⟩

/-- Every pair of entries with the same realized dispatch key has identical
    ports. Repeated aliases are allowed; contradictory aliases are rejected. -/
def Coherent (entries : List RuntimeOperation) : Prop :=
  ∀ left ∈ entries, ∀ right ∈ entries, left.key = right.key → left.ports = right.ports

def checkCoherent (entries : List RuntimeOperation) : Bool :=
  entries.all fun left => entries.all fun right => decide (left.key = right.key → left.ports = right.ports)

theorem check_coherent_iff (entries : List RuntimeOperation) : checkCoherent entries = true ↔ Coherent entries := by
  simp only [checkCoherent, Coherent, List.all_eq_true, decide_eq_true_eq]

def lookupOperations : List RuntimeOperation → Typing.Signature
  | [], _, _ => none
  | entry :: rest, effect, operation =>
      if entry.key = (effect, operation) then some entry.ports else lookupOperations rest effect operation

def operationSignature (entries : List RuntimeOperation) : Typing.Signature :=
  Typing.withCellSignatures (lookupOperations entries)

theorem lookup_operation_sound (known : lookupOperations entries effect operation = some ports) :
    ∃ entry ∈ entries, entry.key = (effect, operation) ∧ entry.ports = ports := by
  induction entries with
  | nil => cases known
  | cons entry rest ih =>
      simp only [lookupOperations] at known
      split at known
      · exact ⟨entry, List.mem_cons_self, by assumption, Option.some.inj known⟩
      · obtain ⟨selected, member, key, type⟩ := ih known
        exact ⟨selected, List.mem_cons_of_mem _ member, key, type⟩

theorem coherent_tail (coherent : Coherent (entry :: rest)) : Coherent rest :=
  fun left l right r => coherent left (List.mem_cons_of_mem _ l) right (List.mem_cons_of_mem _ r)

theorem coherent_lookup_complete (coherent : Coherent entries) (member : entry ∈ entries) :
    lookupOperations entries entry.effect entry.operation = some entry.ports := by
  induction entries with
  | nil => cases member
  | cons first rest ih =>
      simp only [lookupOperations]
      split
      · rename_i same
        exact congrArg some (coherent first List.mem_cons_self entry member same)
      · rename_i different
        rcases List.mem_cons.mp member with same | member
        · subst entry
          exact False.elim (different rfl)
        · exact ih (coherent_tail coherent) member

theorem operation_signature_contains (coherent : Coherent entries) (member : entry ∈ entries) :
    operationSignature entries entry.effect entry.operation = some entry.ports :=
  coherent_lookup_complete coherent member

/-- Checked table order cannot alter a successful signature, including failure
    when no matching declaration exists. Runtime handler order is unaffected. -/
theorem coherent_signature_permutation (coherent : Coherent entries) (permutation : entries.Perm others) :
    operationSignature entries = operationSignature others := by
  have otherCoherent : Coherent others := fun left l right r =>
    coherent left (permutation.mem_iff.mpr l) right (permutation.mem_iff.mpr r)
  funext effect operation
  cases effect with
  | cell key =>
      cases operation with
      | zero => rfl
      | succ operation => cases operation <;> rfl
  | user family arguments =>
      change lookupOperations entries (.user family arguments) operation = lookupOperations others (.user family arguments) operation
      cases first : lookupOperations entries (.user family arguments) operation with
      | some ports =>
          obtain ⟨entry, member, key, type⟩ := lookup_operation_sound first
          have next := coherent_lookup_complete otherCoherent (permutation.mem_iff.mp member)
          have instanceKey : entry.effect = .user family arguments := congrArg Prod.fst key
          have operationKey : entry.operation = operation := congrArg Prod.snd key
          simpa only [instanceKey, operationKey, type] using next.symm
      | none =>
          cases second : lookupOperations others (.user family arguments) operation with
          | none => rfl
          | some ports =>
              obtain ⟨entry, member, key, type⟩ := lookup_operation_sound second
              have earlier := coherent_lookup_complete coherent (permutation.mem_iff.mpr member)
              have instanceKey : entry.effect = .user family arguments := congrArg Prod.fst key
              have operationKey : entry.operation = operation := congrArg Prod.snd key
              rw [instanceKey, operationKey, first] at earlier
              cases earlier

/-- Extending a table requires agreement across the old/new boundary, as well
    as each side's local coherence. Fresh resource atoms alone do not imply it. -/
theorem coherent_append_iff (left right : List RuntimeOperation) :
    Coherent (left ++ right) ↔ Coherent left ∧ Coherent right ∧
      (∀ a ∈ left, ∀ b ∈ right, a.key = b.key → a.ports = b.ports) := by
  constructor
  · intro checked
    exact ⟨fun a am b bm => checked a (List.mem_append_left _ am) b (List.mem_append_left _ bm),
      fun a am b bm => checked a (List.mem_append_right _ am) b (List.mem_append_right _ bm),
      fun a am b bm => checked a (List.mem_append_left _ am) b (List.mem_append_right _ bm)⟩
  · rintro ⟨leftChecked, rightChecked, cross⟩ a am b bm same
    rcases List.mem_append.mp am with al | ar <;> rcases List.mem_append.mp bm with bl | br
    · exact leftChecked a al b bl same
    · exact cross a al b br same
    · exact (cross b bl a ar same.symm).symm
    · exact rightChecked a ar b br same

theorem coherent_extension_preserves_lookup (checked : Coherent (old ++ added))
    (known : lookupOperations old effect operation = some ports) :
    lookupOperations (old ++ added) effect operation = some ports := by
  obtain ⟨entry, member, key, type⟩ := lookup_operation_sound known
  have preserved := coherent_lookup_complete checked (List.mem_append_left added member)
  have sameEffect : entry.effect = effect := congrArg Prod.fst key
  have sameOperation : entry.operation = operation := congrArg Prod.snd key
  simpa only [sameEffect, sameOperation, type] using preserved

/-- An interpretation must respect every declared port at its exact key. This
    judgment allows other keys; lookup_operation_sound separately excludes
    invented entries from the constructed user table. -/
def ContainsEntries (signature : Typing.Signature) (entries : List RuntimeOperation) : Prop :=
  ∀ entry ∈ entries, signature entry.effect entry.operation = some entry.ports

theorem coherent_iff_signature_exists (entries : List RuntimeOperation) :
    Coherent entries ↔ ∃ signature, ContainsEntries signature entries := by
  constructor
  · intro coherent
    exact ⟨operationSignature entries, fun _ member => operation_signature_contains coherent member⟩
  · rintro ⟨signature, contains⟩ left leftMember right rightMember sameKey
    have sameEffect : left.effect = right.effect := congrArg Prod.fst sameKey
    have sameOperation : left.operation = right.operation := congrArg Prod.snd sameKey
    have leftKnown := contains left leftMember
    rw [sameEffect, sameOperation] at leftKnown
    exact Option.some.inj (leftKnown.symm.trans (contains right rightMember))

theorem check_coherent_complete (entries : List RuntimeOperation) :
    checkCoherent entries = true ↔ ∃ signature, ContainsEntries signature entries :=
  (check_coherent_iff entries).trans (coherent_iff_signature_exists entries)

theorem realized_member {relation : α → β → Prop} (entries : ListRealizes relation sources targets)
    (member : source ∈ sources) : ∃ target ∈ targets, relation source target := by
  induction entries with
  | nil => cases member
  | cons checked rest ih =>
      rcases List.mem_cons.mp member with same | member
      · subst source
        exact ⟨_, List.mem_cons_self, checked⟩
      · obtain ⟨target, present, realized⟩ := ih member
        exact ⟨target, List.mem_cons_of_mem _ present, realized⟩

theorem realized_operation_lookup
    (table : ListRealizes (OperationRealizes environment) sources targets)
    (coherent : Coherent targets) (member : source ∈ sources)
    (realized : OperationRealizes environment source target) :
    operationSignature targets target.effect target.operation = some target.ports := by
  obtain ⟨actual, present, checked⟩ := realized_member table member
  rw [operation_realization_unique checked realized] at present
  exact operation_signature_contains coherent present

theorem table_realization_exists (sources : List SourceOperation)
    (available : ∀ entry ∈ sources, NamesBound environment entry.resources) :
    ∃ targets, ListRealizes (OperationRealizes environment) sources targets := by
  induction sources with
  | nil => exact ⟨[], .nil⟩
  | cons source rest ih =>
      obtain ⟨target, checked⟩ := operation_realization_exists source (available source List.mem_cons_self)
      obtain ⟨targets, remaining⟩ := ih (fun entry member => available entry (List.mem_cons_of_mem _ member))
      exact ⟨target :: targets, .cons checked remaining⟩

theorem builtin_read_signature (entries : List RuntimeOperation) (key : Nat) :
    operationSignature entries (.cell key) 0 = some (.reference key, .integer) := rfl

theorem builtin_write_signature (entries : List RuntimeOperation) (key : Nat) :
    operationSignature entries (.cell key) 1 = some (.product (.reference key) .integer, .unit) := rfl

namespace SignatureExamples

def aliases : Environment := (Environment.empty.bind 4 7).bind 5 7

def sourceAlias (binder : Nat) : SourceOperation :=
  ⟨9, [.resource (.bound binder)], 0, .reference (.bound binder), .integer⟩
def targetAlias : RuntimeOperation := ⟨9, [.resource 7], 0, .reference 7, .integer⟩

theorem aliased_declarations_realize :
    ListRealizes (OperationRealizes aliases) [sourceAlias 4, sourceAlias 5] [targetAlias, targetAlias] :=
  .cons (.operation (.cons (.resource (.bound rfl)) .nil) (.reference (.bound rfl)) .integer)
    (.cons (.operation (.cons (.resource (.bound rfl)) .nil) (.reference (.bound rfl)) .integer) .nil)

theorem consistent_aliases_accepted : checkCoherent [targetAlias, targetAlias] = true := by decide

theorem alias_lookup : operationSignature [targetAlias, targetAlias] (.user 9 [.resource 7]) 0 =
    some (.reference 7, .integer) := by
  apply operation_signature_contains (entry := targetAlias) ((check_coherent_iff _).mp consistent_aliases_accepted)
  exact List.mem_cons_self

def badSource : SourceOperation := ⟨9, [.resource (.bound 5)], 0, .reference (.bound 5), .unit⟩
def badTarget : RuntimeOperation := ⟨9, [.resource 7], 0, .reference 7, .unit⟩

theorem conflicting_aliases_realize :
    ListRealizes (OperationRealizes aliases) [sourceAlias 4, badSource] [targetAlias, badTarget] :=
  .cons (.operation (.cons (.resource (.bound rfl)) .nil) (.reference (.bound rfl)) .integer)
    (.cons (.operation (.cons (.resource (.bound rfl)) .nil) (.reference (.bound rfl)) .unit) .nil)

theorem conflicting_aliases_have_no_signature :
    ¬ ∃ signature, ContainsEntries signature [targetAlias, badTarget] := by
  intro signature
  have accepted := (check_coherent_complete _).mpr signature
  have rejected : checkCoherent [targetAlias, badTarget] = false := by decide
  rw [rejected] at accepted
  cases accepted

/-- Realizing metadata is insufficient to establish signature coherence. -/
theorem realization_does_not_imply_coherence :
    ListRealizes (OperationRealizes aliases) [sourceAlias 4, badSource] [targetAlias, badTarget] ∧
      ¬ Coherent [targetAlias, badTarget] :=
  ⟨conflicting_aliases_realize,
    fun coherent => conflicting_aliases_have_no_signature ((coherent_iff_signature_exists _).mp coherent)⟩

def callableInput : Ty := .function .unit .unit [.cell 8] [8]
def callableOperation : RuntimeOperation := ⟨11, [], 0, callableInput, .unit⟩

theorem callable_outside_instance_accepted :
    checkCoherent [callableOperation] = true ∧
      operationSignature [callableOperation] (.user 11 []) 0 = some (callableInput, .unit) ∧
      8 ∈ callableInput.resources ∧ 8 ∉ callableOperation.effect.resources := by
  exact ⟨by decide, rfl, by decide, by decide⟩

theorem callable_example_exceeds_restricted_signature_support :
    ¬ Typing.SignatureSupported (operationSignature [callableOperation]) := by
  intro supported
  have impossible := supported (.user 11 []) 0 callableInput .unit rfl
    (by decide : 8 ∈ callableInput.resources ++ Ty.unit.resources)
  cases impossible

def oldEnvironment : Environment := Environment.empty.bind 4 0
def newEnvironment : Environment := Environment.empty.bind 4 1
def oldOperation : RuntimeOperation := ⟨9, [.resource 0], 0, .reference 0, .integer⟩

theorem older_operation_ports_keep_activation :
    ((sourceAlias 4).instantiate oldEnvironment).instantiate newEnvironment = freezeOperation oldOperation :=
  realized_operation_cannot_be_rebound (first := oldEnvironment) (source := sourceAlias 4) (target := oldOperation)
    (.operation (.cons (.resource (.bound rfl)) .nil) (.reference (.bound rfl)) .integer) newEnvironment

def sourceCallable : SourceOperation :=
  ⟨11, [], 0, .function .unit .unit [.cell (.bound 4)] [.bound 4], .unit⟩
def runtimeCallable (key : Nat) : RuntimeOperation :=
  ⟨11, [], 0, .function .unit .unit [.cell key] [key], .unit⟩

theorem callable_realizes_old : OperationRealizes oldEnvironment sourceCallable (runtimeCallable 0) :=
  .operation .nil (.function .unit .unit (.cons (.cell (.bound rfl)) .nil) (.cons (.bound rfl) .nil)) .unit

theorem callable_realizes_new : OperationRealizes newEnvironment sourceCallable (runtimeCallable 1) :=
  .operation .nil (.function .unit .unit (.cons (.cell (.bound rfl)) .nil) (.cons (.bound rfl) .nil)) .unit

/-- Abstract descriptors can be individually coherent and use different fresh
    atoms while conflicting at the same key. This is not an authenticated Core
    declaration: authentication must rule it out or justify the intended ports. -/
theorem fresh_atoms_do_not_imply_coherent_extension :
    (0 : Nat) ≠ 1 ∧ Coherent [runtimeCallable 0] ∧ Coherent [runtimeCallable 1] ∧
      ¬ Coherent [runtimeCallable 0, runtimeCallable 1] := by
  refine ⟨by decide, (check_coherent_iff _).mp (by decide), (check_coherent_iff _).mp (by decide), ?_⟩
  intro coherent
  have accepted := (check_coherent_iff _).mpr coherent
  have rejected : checkCoherent [runtimeCallable 0, runtimeCallable 1] = false := by decide
  rw [rejected] at accepted
  cases accepted

/-- All four function metadata positions remain frozen, including a nested result. -/
theorem older_function_metadata_keeps_activation :
    (Instantiation.Examples.sourceType.instantiate Instantiation.Examples.outer).instantiate Instantiation.Examples.inner =
      freezeType Instantiation.Examples.oldType :=
  realized_type_cannot_be_rebound Instantiation.Examples.outer_type_realized _

end SignatureExamples

end Ash.OneShot.Instantiation

#print axioms Ash.OneShot.Instantiation.type_instantiation_realizes
#print axioms Ash.OneShot.Instantiation.realized_type_cannot_be_rebound
#print axioms Ash.OneShot.Instantiation.type_instantiation_resources
#print axioms Ash.OneShot.Instantiation.operation_realization_exists
#print axioms Ash.OneShot.Instantiation.operation_instantiation_realizes
#print axioms Ash.OneShot.Instantiation.check_coherent_iff
#print axioms Ash.OneShot.Instantiation.coherent_lookup_complete
#print axioms Ash.OneShot.Instantiation.coherent_signature_permutation
#print axioms Ash.OneShot.Instantiation.check_coherent_complete
#print axioms Ash.OneShot.Instantiation.realized_operation_lookup
#print axioms Ash.OneShot.Instantiation.table_realization_exists
#print axioms Ash.OneShot.Instantiation.builtin_read_signature
#print axioms Ash.OneShot.Instantiation.builtin_write_signature
#print axioms Ash.OneShot.Instantiation.SignatureExamples.alias_lookup
#print axioms Ash.OneShot.Instantiation.SignatureExamples.realization_does_not_imply_coherence
#print axioms Ash.OneShot.Instantiation.SignatureExamples.callable_outside_instance_accepted
#print axioms Ash.OneShot.Instantiation.SignatureExamples.callable_example_exceeds_restricted_signature_support
#print axioms Ash.OneShot.Instantiation.SignatureExamples.older_operation_ports_keep_activation
#print axioms Ash.OneShot.Instantiation.SignatureExamples.older_function_metadata_keeps_activation

#print axioms Ash.OneShot.Instantiation.coherent_append_iff
#print axioms Ash.OneShot.Instantiation.coherent_extension_preserves_lookup
#print axioms Ash.OneShot.Instantiation.SignatureExamples.fresh_atoms_do_not_imply_coherent_extension
