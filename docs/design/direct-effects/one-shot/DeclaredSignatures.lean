import ScopedSignatures

/-!
Declaration-derived signatures for the resource-parameter fragment. A fixed
registry chooses the family and positional operation; ordered arguments bind
the declared resource parameters, and structural type realization fixes ports.
This models one part of Core authentication, not the full Core declaration
validator, general kinds/type parameters, or expression typing.
-/

namespace Ash.OneShot.Instantiation

structure OperationTemplate where
  input : ValueType
  output : ValueType
  deriving DecidableEq, Repr

def OperationTemplate.resources (operation : OperationTemplate) : List ResourceName :=
  operation.input.resources ++ operation.output.resources

structure FamilyTemplate where
  parameters : List Nat
  operations : List OperationTemplate
  deriving DecidableEq, Repr

/-- Declaration metadata names only its own parameters, never runtime atoms. -/
def DeclaredName (parameters : List Nat) : ResourceName → Prop
  | .bound name => name ∈ parameters
  | .activation _ => False

instance (parameters : List Nat) (name : ResourceName) : Decidable (DeclaredName parameters name) := by
  cases name <;> unfold DeclaredName <;> infer_instance

def FamilyValid (family : FamilyTemplate) : Prop :=
  family.parameters.Nodup ∧ family.operations ≠ [] ∧
    ∀ operation ∈ family.operations, ∀ name ∈ operation.resources, DeclaredName family.parameters name

def checkFamily (family : FamilyTemplate) : Bool :=
  decide family.parameters.Nodup && decide (family.operations ≠ []) &&
    family.operations.all fun operation => operation.resources.all fun name => decide (DeclaredName family.parameters name)

theorem check_family_iff (family : FamilyTemplate) : checkFamily family = true ↔ FamilyValid family := by
  simp only [checkFamily, FamilyValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc]

/-- Simultaneous positional binding for resource arguments. Wrong arity and
    non-resource arguments fail rather than inventing an activation. -/
def parameterEnvironment : List Nat → List TypeArgument → Option Environment
  | [], [] => some Environment.empty
  | parameter :: rest, .resource key :: arguments =>
      (parameterEnvironment rest arguments).map fun environment => environment.bind parameter key
  | _, _ => none

theorem parameter_environment_binds (built : parameterEnvironment parameters arguments = some environment) :
    ∀ parameter ∈ parameters, ∃ key, environment parameter = some key := by
  induction parameters generalizing arguments environment with
  | nil => intro parameter member; cases member
  | cons parameter rest ih =>
      cases arguments with
      | nil => cases built
      | cons argument arguments =>
          cases argument with
          | nominal | apply => cases built
          | resource key =>
              cases tail : parameterEnvironment rest arguments with
              | none => simp [parameterEnvironment, tail] at built
              | some preceding =>
                  simp only [parameterEnvironment, tail, Option.map_some, Option.some.injEq] at built
                  subst environment
                  intro name member
                  by_cases same : name = parameter
                  · exact ⟨key, by simp [Environment.bind, same]⟩
                  · obtain ⟨old, known⟩ := ih tail name ((List.mem_cons.mp member).resolve_left same)
                    exact ⟨old, by simp [Environment.bind, same, known]⟩

theorem parameter_environment_length (built : parameterEnvironment parameters arguments = some environment) :
    parameters.length = arguments.length := by
  induction parameters generalizing arguments environment with
  | nil => cases arguments <;> first | rfl | cases built
  | cons parameter rest ih =>
      cases arguments with
      | nil => cases built
      | cons argument arguments =>
          cases argument with
          | nominal | apply => cases built
          | resource key =>
              cases tail : parameterEnvironment rest arguments with
              | none => simp [parameterEnvironment, tail] at built
              | some preceding => exact congrArg Nat.succ (ih tail)

theorem declared_names_are_bound
    (declared : ∀ name ∈ names, DeclaredName parameters name)
    (built : parameterEnvironment parameters arguments = some environment) : NamesBound environment names := by
  intro name member
  have inScope := declared name member
  cases name with
  | activation => cases inScope
  | bound parameter => exact parameter_environment_binds built parameter inScope

abbrev DeclarationRegistry := Nat → Option FamilyTemplate

/-- The selected registry entry and operation position determine the templates;
    the complete exact argument vector determines their substitution. -/
inductive DeclaredOperation (registry : DeclarationRegistry) : RuntimeOperation → Prop where
  | declared (familyKnown : registry family = some declaration)
      (valid : FamilyValid declaration)
      (operationKnown : declaration.operations[operation]? = some template)
      (argumentsBound : parameterEnvironment declaration.parameters arguments = some environment)
      (inputRealized : TypeRealizes environment template.input input)
      (outputRealized : TypeRealizes environment template.output output) :
      DeclaredOperation registry ⟨family, arguments, operation, input, output⟩

/-- Lookup, argument binding and type realization are each functional. Thus
    declaration-derived ports agree without a per-table coherence premise. -/
theorem declared_operation_ports_unique
    (leftChecked : DeclaredOperation registry left) (rightChecked : DeclaredOperation registry right)
    (sameKey : left.key = right.key) : left.ports = right.ports := by
  cases leftChecked with
  | declared leftFamily leftValid leftOperation leftArguments leftInput leftOutput =>
      cases rightChecked with
      | declared rightFamily rightValid rightOperation rightArguments rightInput rightOutput =>
          simp only [RuntimeOperation.key, RuntimeOperation.effect, Prod.mk.injEq, Instance.user.injEq] at sameKey
          obtain ⟨⟨sameFamily, sameArguments⟩, sameOperation⟩ := sameKey
          subst sameFamily
          subst sameArguments
          subst sameOperation
          have sameDeclaration := Option.some.inj (leftFamily.symm.trans rightFamily)
          subst sameDeclaration
          have sameTemplate := Option.some.inj (leftOperation.symm.trans rightOperation)
          subst sameTemplate
          have sameEnvironment := Option.some.inj (leftArguments.symm.trans rightArguments)
          subst sameEnvironment
          exact Prod.ext (type_realization_unique leftInput rightInput) (type_realization_unique leftOutput rightOutput)

theorem declared_operation_exists
    (familyKnown : registry family = some declaration) (valid : FamilyValid declaration)
    (operationKnown : declaration.operations[operation]? = some template)
    (argumentsBound : parameterEnvironment declaration.parameters arguments = some environment) :
    ∃ input output, DeclaredOperation registry ⟨family, arguments, operation, input, output⟩ := by
  have member : template ∈ declaration.operations := List.mem_of_getElem? operationKnown
  have inScope := valid.2.2 template member
  have bound := declared_names_are_bound inScope argumentsBound
  obtain ⟨inputNames, outputNames⟩ := names_bound_append bound
  obtain ⟨input, inputRealized⟩ := type_realization_exists template.input inputNames
  obtain ⟨output, outputRealized⟩ := type_realization_exists template.output outputNames
  exact ⟨input, output, .declared familyKnown valid operationKnown argumentsBound inputRealized outputRealized⟩

def DeclaredTable (registry : DeclarationRegistry) (entries : List RuntimeOperation) : Prop :=
  ∀ entry ∈ entries, DeclaredOperation registry entry

theorem declared_table_coherent (checked : DeclaredTable registry entries) : Coherent entries :=
  fun left l right r => declared_operation_ports_unique (checked left l) (checked right r)

theorem declared_table_passes_check (checked : DeclaredTable registry entries) : checkCoherent entries = true :=
  (check_coherent_iff entries).mpr (declared_table_coherent checked)

theorem declared_table_signature_contains (checked : DeclaredTable registry entries) :
    ContainsEntries (operationSignature entries) entries :=
  fun _ member => operation_signature_contains (declared_table_coherent checked) member

/-- Registry extension preserves complete old declarations, not just identity
    membership. Changed parameter or operation types are not extensions. -/
def DeclarationExtension (before after : DeclarationRegistry) : Prop :=
  ∀ family declaration, before family = some declaration → after family = some declaration

theorem declared_operation_extension (checked : DeclaredOperation before entry)
    (extension : DeclarationExtension before after) : DeclaredOperation after entry := by
  cases checked with
  | declared family valid operation arguments input output =>
      exact .declared (extension _ _ family) valid operation arguments input output

theorem declared_table_extension (checked : DeclaredTable before entries)
    (extension : DeclarationExtension before after) : DeclaredTable after entries :=
  fun entry member => declared_operation_extension (checked entry member) extension

theorem declared_tables_append (left : DeclaredTable registry old) (right : DeclaredTable registry added) :
    DeclaredTable registry (old ++ added) := by
  intro entry member
  rcases List.mem_append.mp member with earlier | later
  · exact left entry earlier
  · exact right entry later

theorem declared_extension_coherent (oldChecked : DeclaredTable before old)
    (extension : DeclarationExtension before after) (newChecked : DeclaredTable after added) :
    Coherent (old ++ added) :=
  declared_table_coherent (declared_tables_append (declared_table_extension oldChecked extension) newChecked)

theorem declared_extension_preserves_lookup (oldChecked : DeclaredTable before old)
    (extension : DeclarationExtension before after) (newChecked : DeclaredTable after added)
    (known : lookupOperations old effect operation = some ports) :
    lookupOperations (old ++ added) effect operation = some ports :=
  coherent_extension_preserves_lookup (declared_extension_coherent oldChecked extension newChecked) known

theorem declared_realized_operation_lookup
    (table : ListRealizes (OperationRealizes environment) sources targets)
    (declared : DeclaredTable registry targets) (member : source ∈ sources)
    (realized : OperationRealizes environment source target) :
    operationSignature targets target.effect target.operation = some target.ports :=
  realized_operation_lookup table (declared_table_coherent declared) member realized

theorem declared_operation_argument_count (checked : DeclaredOperation registry entry) :
    ∃ declaration, registry entry.family = some declaration ∧ declaration.parameters.length = entry.arguments.length := by
  cases checked with
  | declared family valid operation arguments input output =>
      exact ⟨_, family, parameter_environment_length arguments⟩

namespace DeclarationExamples

def ask : FamilyTemplate := ⟨[4], [⟨.reference (.bound 4), .integer⟩]⟩
def callback : FamilyTemplate :=
  ⟨[4], [⟨.function .unit .unit [.cell (.bound 4)] [.bound 4], .unit⟩]⟩
def registry : DeclarationRegistry := fun family =>
  if family = 9 then some ask else if family = 11 then some callback else none

theorem ask_valid : FamilyValid ask := (check_family_iff _).mp (by decide)
theorem callback_valid : FamilyValid callback := (check_family_iff _).mp (by decide)

def askAt (key : Nat) : RuntimeOperation := ⟨9, [.resource key], 0, .reference key, .integer⟩
def callbackAt (key : Nat) : RuntimeOperation :=
  ⟨11, [.resource key], 0, .function .unit .unit [.cell key] [key], .unit⟩

theorem ask_declared (key : Nat) : DeclaredOperation registry (askAt key) :=
  .declared rfl ask_valid rfl (environment := Environment.empty.bind 4 key) rfl (.reference (.bound rfl)) .integer

theorem callback_declared (key : Nat) : DeclaredOperation registry (callbackAt key) :=
  .declared rfl callback_valid rfl (environment := Environment.empty.bind 4 key) rfl
    (.function .unit .unit (.cons (.cell (.bound rfl)) .nil) (.cons (.bound rfl) .nil)) .unit

theorem consistent_aliases_declared : DeclaredTable registry [SignatureExamples.targetAlias, SignatureExamples.targetAlias] := by
  intro entry member
  rcases List.mem_cons.mp member with same | remaining
  · subst entry; exact ask_declared 7
  · obtain rfl := List.mem_singleton.mp remaining
    exact ask_declared 7

theorem alias_signature_from_declaration :
    operationSignature [SignatureExamples.targetAlias, SignatureExamples.targetAlias] (.user 9 [.resource 7]) 0 =
      some (.reference 7, .integer) :=
  declared_table_signature_contains consistent_aliases_declared _ List.mem_cons_self

theorem conflicting_result_not_declared : ¬ DeclaredOperation registry SignatureExamples.badTarget := by
  intro checked
  have impossible := declared_operation_ports_unique (ask_declared 7) checked rfl
  cases impossible

theorem fresh_callbacks_extend_coherently : Coherent [callbackAt 0, callbackAt 1] := by
  apply declared_table_coherent (registry := registry)
  intro entry member
  rcases List.mem_cons.mp member with same | remaining
  · subst entry; exact callback_declared 0
  · obtain rfl := List.mem_singleton.mp remaining
    exact callback_declared 1

/-- The earlier abstract same-key counterexample omits the declared argument. -/
theorem missing_callback_argument_rejected (key : Nat) :
    ¬ DeclaredOperation registry (SignatureExamples.runtimeCallable key) := by
  intro checked
  obtain ⟨declaration, known, length⟩ := declared_operation_argument_count checked
  have selected : declaration = callback := Option.some.inj known.symm
  subst declaration
  cases length

theorem undeclared_parameter_rejected :
    checkFamily ⟨[], [⟨.reference (.bound 4), .integer⟩]⟩ = false := by decide

theorem literal_activation_rejected :
    checkFamily ⟨[], [⟨.reference (.activation 8), .integer⟩]⟩ = false := by decide

theorem duplicate_parameters_rejected :
    checkFamily ⟨[4, 4], [⟨.reference (.bound 4), .integer⟩]⟩ = false := by decide

theorem empty_api_rejected : checkFamily ⟨[4], []⟩ = false := by decide

/-- Resource-name formation alone does not authenticate latent effect names. -/
theorem family_check_does_not_validate_latent_effects :
    checkFamily ⟨[], [⟨.function .unit .unit [.user 99 []] [], .unit⟩]⟩ = true ∧
      registry 99 = none := ⟨by decide, rfl⟩

theorem wrong_arity_and_argument_form_rejected :
    parameterEnvironment [4] [] = none ∧ parameterEnvironment [4] [.nominal 7] = none := ⟨rfl, rfl⟩

theorem unknown_family_rejected : ¬ DeclaredOperation registry ⟨12, [], 0, .unit, .unit⟩ := by
  intro checked
  cases checked with
  | declared known valid operation arguments input output => cases known

theorem unknown_operation_rejected : ¬ DeclaredOperation registry ⟨9, [.resource 7], 1, .unit, .unit⟩ := by
  intro checked
  cases checked with
  | declared known valid operation arguments input output =>
      have selected : _ = ask := Option.some.inj known.symm
      subst selected
      cases operation

end DeclarationExamples

end Ash.OneShot.Instantiation

#print axioms Ash.OneShot.Instantiation.check_family_iff
#print axioms Ash.OneShot.Instantiation.parameter_environment_binds
#print axioms Ash.OneShot.Instantiation.parameter_environment_length
#print axioms Ash.OneShot.Instantiation.declared_operation_ports_unique
#print axioms Ash.OneShot.Instantiation.declared_operation_exists
#print axioms Ash.OneShot.Instantiation.declared_table_coherent
#print axioms Ash.OneShot.Instantiation.declared_extension_coherent
#print axioms Ash.OneShot.Instantiation.declared_extension_preserves_lookup
#print axioms Ash.OneShot.Instantiation.declared_realized_operation_lookup
#print axioms Ash.OneShot.Instantiation.DeclarationExamples.alias_signature_from_declaration
#print axioms Ash.OneShot.Instantiation.DeclarationExamples.conflicting_result_not_declared
#print axioms Ash.OneShot.Instantiation.DeclarationExamples.fresh_callbacks_extend_coherently
#print axioms Ash.OneShot.Instantiation.DeclarationExamples.missing_callback_argument_rejected
#print axioms Ash.OneShot.Instantiation.DeclarationExamples.literal_activation_rejected
#print axioms Ash.OneShot.Instantiation.DeclarationExamples.unknown_family_rejected
#print axioms Ash.OneShot.Instantiation.DeclarationExamples.unknown_operation_rejected

#print axioms Ash.OneShot.Instantiation.DeclarationExamples.family_check_does_not_validate_latent_effects
