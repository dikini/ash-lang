import OperationReturns

/-!
Result bounds derived from the existing resource-parameter declarations.
Formal declaration parameters bind to source ResourceNames before acquisition;
opening preserves this binding and its stored-result bound. Runtime signature
compilation uses the same declaration and the existing type realization.
-/

namespace Ash.OneShot.DeclarationResults
open Instantiation Syntax ScopedExpressions ScopedPorts
open TemplateSupport (Bound merge mapBound lift)
open ContinuationBounds (portBound)

abbrev NameEnvironment := Nat → Option ResourceName

def namedParameters : List Nat → List Argument → Option NameEnvironment
  | [], [] => some (fun _ => none)
  | parameter :: rest, .resource name :: arguments =>
      (namedParameters rest arguments).map fun environment other =>
        if other = parameter then some name else environment other
  | _, _ => none

def openNames (resources : Instantiation.Environment) (environment : NameEnvironment) : NameEnvironment :=
  fun name => (environment name).map (ResourceName.instantiate resources)

def freezeEnvironment (environment : Instantiation.Environment) : NameEnvironment :=
  fun name => (environment name).map ResourceName.activation

theorem named_parameters_open (parameters : List Nat) (arguments : List Argument) :
    namedParameters parameters (arguments.map (Argument.instantiate resources)) =
      (namedParameters parameters arguments).map (openNames resources) := by
  induction parameters generalizing arguments with
  | nil => cases arguments <;> rfl
  | cons parameter rest ih =>
      cases arguments with
      | nil => rfl
      | cons argument arguments => cases argument with
          | nominal | apply => rfl
          | resource name =>
              simp only [List.map_cons, Argument.instantiate, namedParameters, ih]
              cases namedParameters rest arguments with
              | none => rfl
              | some environment =>
                  apply congrArg some
                  funext other
                  by_cases same : other = parameter <;> simp [openNames, same]

theorem named_parameters_frozen (parameters : List Nat) (arguments : List TypeArgument) :
    namedParameters parameters (arguments.map freezeArgument) =
      (parameterEnvironment parameters arguments).map freezeEnvironment := by
  induction parameters generalizing arguments with
  | nil => cases arguments <;> rfl
  | cons parameter rest ih =>
      cases arguments with
      | nil => rfl
      | cons argument arguments => cases argument with
          | nominal | apply => rfl
          | resource identity =>
              simp only [List.map_cons, freezeArgument, namedParameters, parameterEnvironment, ih]
              cases parameterEnvironment rest arguments with
              | none => rfl
              | some environment =>
                  apply congrArg some
                  funext other
                  by_cases same : other = parameter <;> simp [freezeEnvironment, Environment.bind, same]

def nameBound (environment : NameEnvironment) : ResourceName → Bound
  | .activation identity => some [.activation identity]
  | .bound name => (environment name).map fun actual => [actual]

def typeBound (environment : NameEnvironment) : ValueType → Bound
  | .unit | .boolean | .integer => some []
  | .reference name => nameBound environment name
  | .product left right => merge (typeBound environment left) (typeBound environment right)
  | .function _ _ _ _ => none

theorem name_bound_open (name : ResourceName) :
    nameBound (openNames resources environment) name = mapBound resources (nameBound environment name) := by
  cases name with
  | activation => rfl
  | bound parameter => cases known : environment parameter <;> simp [nameBound, openNames, mapBound, known]

theorem type_bound_open (type : ValueType) :
    typeBound (openNames resources environment) type = mapBound resources (typeBound environment type) := by
  induction type with
  | unit | boolean | integer | function => rfl
  | reference name => exact name_bound_open name
  | product left right ihLeft ihRight => rw [typeBound, ihLeft, ihRight, ← TemplateSupport.map_merge]; rfl

theorem name_bound_realizes (realized : NameRealizes environment source target) :
    nameBound (freezeEnvironment environment) source = lift (some [target]) := by
  cases realized with
  | activation => rfl
  | bound known => simp [nameBound, freezeEnvironment, known, lift]

theorem type_bound_realizes (realized : TypeRealizes environment source target) :
    typeBound (freezeEnvironment environment) source = lift (portBound (eraseType target)).support := by
  induction realized with
  | unit | boolean | integer | function => rfl
  | reference name => exact name_bound_realizes name
  | product left right ihLeft ihRight =>
      simp only [typeBound, ihLeft, ihRight]
      rw [← TemplateSupport.lift_merge]
      rfl

/-- Declaration validation and positional argument binding occur before the
    output bound is read. Callable declaration metadata never bounds captures. -/
def operationBound (registry : DeclarationRegistry) : Effect → Nat → Bound
  | .cell _, 0 | .cell _, 1 => some []
  | .cell _, _ => none
  | .user family arguments, operation => do
      let declaration ← registry family
      if checkFamily declaration then
        let template ← declaration.operations[operation]?
        let environment ← namedParameters declaration.parameters arguments
        typeBound environment template.output
      else none

theorem operation_bound_open (effect : Effect) (operation : Nat) :
    operationBound registry (effect.instantiate resources) operation =
      mapBound resources (operationBound registry effect operation) := by
  cases effect with
  | cell name => cases operation with
      | zero => rfl
      | succ operation => cases operation <;> rfl
  | user family arguments =>
      simp only [Effect.instantiate, operationBound]
      cases declarationKnown : registry family with
      | none => rfl
      | some declaration =>
          dsimp only [bind, Option.bind]
          split
          · cases operationKnown : declaration.operations[operation]? with
            | none => rfl
            | some template =>
                rw [named_parameters_open]
                dsimp only [bind, Option.bind]
                cases namedParameters declaration.parameters arguments with
                | none => rfl
                | some environment => exact type_bound_open template.output
          · rfl

def decodeType : ValueType → Option Ty
  | .unit => some .unit
  | .boolean => some .boolean
  | .integer => some .integer
  | .reference name => (OperationResults.decodeName name).map Ty.reference
  | .product left right => do
      let first ← decodeType left
      let second ← decodeType right
      pure (.product first second)
  | .function input output requests retained => do
      let first ← decodeType input
      let second ← decodeType output
      let effects ← requests.mapM OperationResults.decodeEffect
      let captures ← retained.mapM OperationResults.decodeName
      pure (.function first second effects captures)

theorem mapM_frozen_effects (effects : List Instance) :
    (effects.map freezeEffect).mapM OperationResults.decodeEffect = some effects := by
  induction effects with
  | nil => rfl
  | cons first rest ih => simp [List.mapM_cons, OperationResults.decode_frozen_effect, ih]

theorem mapM_frozen_names (names : List Nat) :
    (names.map ResourceName.activation).mapM OperationResults.decodeName = some names := by
  induction names with
  | nil => rfl
  | cons first rest ih => simp [List.mapM_cons, OperationResults.decodeName, ih]

theorem decode_frozen_type (type : Ty) : decodeType (freezeType type) = some type := by
  induction type with
  | unit | boolean | integer | reference => rfl
  | product left right ihLeft ihRight => simp [freezeType, decodeType, ihLeft, ihRight]
  | function input output requests retained ihInput ihOutput =>
      simp only [freezeType, decodeType, ihInput, ihOutput, mapM_frozen_effects, mapM_frozen_names]
      rfl

theorem decode_realized_type (realized : TypeRealizes environment source target) :
    decodeType (source.instantiate environment) = some target := by
  rw [type_instantiation_realizes realized, decode_frozen_type]

def userSignature (registry : DeclarationRegistry) : ScopedPorts.Signature
  | .cell _, _ => none
  | .user family arguments, operation => do
      let declaration ← registry family
      if checkFamily declaration then
        let template ← declaration.operations[operation]?
        let environment ← parameterEnvironment declaration.parameters arguments
        let input ← decodeType (template.input.instantiate environment)
        let output ← decodeType (template.output.instantiate environment)
        pure (eraseType input, eraseType output)
      else none

def signature (registry : DeclarationRegistry) : ScopedPorts.Signature := withCellSignatures (userSignature registry)

theorem declared_signature_known (declared : DeclaredOperation registry entry) :
    signature registry entry.effect entry.operation = some (eraseType entry.input, eraseType entry.output) := by
  cases declared with
  | declared family valid operation arguments input output =>
      simp [signature, withCellSignatures, userSignature, RuntimeOperation.effect, family,
        (check_family_iff _).mpr valid, operation, arguments, decode_realized_type input, decode_realized_type output]

theorem declared_operation_bound (declared : DeclaredOperation registry entry) :
    operationBound registry (freezeEffect entry.effect) entry.operation =
      lift (portBound (eraseType entry.output)).support := by
  cases declared with
  | declared family valid operation arguments input output =>
      simp [RuntimeOperation.effect, freezeEffect, operationBound, family,
        (check_family_iff _).mpr valid, operation, named_parameters_frozen, arguments,
        type_bound_realizes output]

/-- Both successful and failed lookups agree. A missing family, malformed
    declaration, wrong operation position or wrong argument vector stays unknown. -/
theorem operation_bound_runtime (effect : Instance) (operation : Nat) :
    operationBound registry (freezeEffect effect) operation =
      lift (OperationResults.operationBound (signature registry) (freezeEffect effect) operation).support := by
  cases effect with
  | cell identity => cases operation with
      | zero => rfl
      | succ operation => cases operation <;> rfl
  | user family arguments =>
      cases familyKnown : registry family with
      | none => simp [operationBound, freezeEffect, familyKnown, OperationResults.operationBound,
          OperationResults.decode_frozen_arguments, OperationResults.decodeEffect, signature,
          withCellSignatures, userSignature, lift, ResultSummaries.Summary.support]
      | some declaration =>
          cases validCheck : checkFamily declaration with
          | false => simp [operationBound, freezeEffect, familyKnown, validCheck, OperationResults.operationBound,
              OperationResults.decode_frozen_arguments, OperationResults.decodeEffect, signature,
              withCellSignatures, userSignature, lift, ResultSummaries.Summary.support]
          | true =>
              cases operationKnown : declaration.operations[operation]? with
              | none => simp [operationBound, freezeEffect, familyKnown, validCheck, operationKnown,
                  OperationResults.operationBound, OperationResults.decode_frozen_arguments,
                  OperationResults.decodeEffect, signature, withCellSignatures, userSignature,
                  lift, ResultSummaries.Summary.support]
              | some template =>
                  cases argumentsBound : parameterEnvironment declaration.parameters arguments with
                  | none => simp [operationBound, freezeEffect, familyKnown, validCheck, operationKnown,
                      named_parameters_frozen, argumentsBound, OperationResults.operationBound,
                      OperationResults.decode_frozen_arguments, OperationResults.decodeEffect,
                      signature, withCellSignatures, userSignature, lift, ResultSummaries.Summary.support]
                  | some environment =>
                      obtain ⟨input, output, declared⟩ := declared_operation_exists familyKnown
                        ((check_family_iff _).mp validCheck) operationKnown argumentsBound
                      have bound := declared_operation_bound declared
                      have known := declared_signature_known declared
                      have runtime := OperationResults.operation_bound_known known
                      exact bound.trans (congrArg (fun summary => lift summary.support) runtime.symm)

theorem closed_argument_frozen (closed : source.freeNames = []) :
    ∃ target, source = freezeArgument target := by
  induction source with
  | nominal identity => exact ⟨.nominal identity, rfl⟩
  | resource name => cases name with
      | activation identity => exact ⟨.resource identity, rfl⟩
      | bound name => cases closed
  | apply head argument ihHead ihArgument =>
      obtain ⟨left, right⟩ := List.append_eq_nil_iff.mp closed
      obtain ⟨first, rfl⟩ := ihHead left
      obtain ⟨second, rfl⟩ := ihArgument right
      exact ⟨.apply first second, rfl⟩

theorem closed_arguments_frozen (arguments : List Argument)
    (closed : arguments.flatMap Argument.freeNames = []) :
    ∃ targets : List TypeArgument, arguments = targets.map freezeArgument := by
  induction arguments with
  | nil => exact ⟨[], rfl⟩
  | cons first rest ih =>
      obtain ⟨left, right⟩ := List.append_eq_nil_iff.mp closed
      obtain ⟨target, rfl⟩ := closed_argument_frozen left
      obtain ⟨targets, rfl⟩ := ih right
      exact ⟨target :: targets, rfl⟩

theorem closed_effect_frozen (closed : effect.freeNames = []) :
    ∃ target, effect = freezeEffect target := by
  cases effect with
  | cell name => cases name with
      | activation identity => exact ⟨.cell identity, rfl⟩
      | bound name => cases closed
  | user family arguments =>
      obtain ⟨targets, rfl⟩ := closed_arguments_frozen arguments closed
      exact ⟨.user family targets, rfl⟩

theorem closed_operation_bound_runtime (closed : effect.freeNames = []) :
    operationBound registry effect operation =
      lift (OperationResults.operationBound (signature registry) effect operation).support := by
  obtain ⟨target, rfl⟩ := closed_effect_frozen closed
  exact operation_bound_runtime target operation

namespace Examples

theorem positional_aliases_preserved :
    (namedParameters [0, 1] [.resource (.bound 4), .resource (.bound 4)]).map
      (fun environment => (environment 0, environment 1)) = some (some (.bound 4), some (.bound 4)) := rfl

theorem wrong_arity_rejected : namedParameters [0] [] = none := rfl

theorem nonresource_argument_rejected : namedParameters [0] [.nominal 7] = none := rfl

theorem nested_resource_argument_rejected :
    namedParameters [0] [.apply (.nominal 7) (.resource (.bound 4))] = none := rfl

def duplicateParameters : FamilyTemplate := ⟨[0, 0], [⟨.unit, .reference (.bound 0)⟩]⟩
def undeclaredParameter : FamilyTemplate := ⟨[0], [⟨.unit, .reference (.bound 1)⟩]⟩
def runtimeAtom : FamilyTemplate := ⟨[], [⟨.unit, .reference (.activation 7)⟩]⟩

theorem invalid_declarations_rejected :
    operationBound (fun _ => some duplicateParameters) (.user 9 [.resource (.bound 4), .resource (.bound 5)]) 0 = none ∧
    operationBound (fun _ => some undeclaredParameter) (.user 9 [.resource (.bound 4)]) 0 = none ∧
    operationBound (fun _ => some runtimeAtom) (.user 9 []) 0 = none := by decide

theorem unknown_family_and_operation_rejected :
    operationBound (fun _ => none) (.user 9 []) 0 = none ∧
    operationBound DeclarationExamples.registry (.user 9 [.resource (.bound 4)]) 1 = none := by decide

theorem same_declaration_at_distinct_activations :
    signature DeclarationExamples.registry (.user 9 [.resource 7]) 0 = some (.reference 7, .integer) ∧
    signature DeclarationExamples.registry (.user 9 [.resource 8]) 0 = some (.reference 8, .integer) :=
  ⟨declared_signature_known (DeclarationExamples.ask_declared 7),
    declared_signature_known (DeclarationExamples.ask_declared 8)⟩

theorem builtins_ignore_user_registry (registry : DeclarationRegistry) (identity : Nat) :
    signature registry (.cell identity) 0 = some (.reference identity, .integer) ∧
    signature registry (.cell identity) 1 = some (.product (.reference identity) .integer, .unit) := ⟨rfl, rfl⟩

/-- A scalar output does not excuse an ill-formed input declaration. -/
theorem malformed_input_rejected_before_result_analysis :
    operationBound (fun _ => some (⟨[], [⟨.reference (.bound 0), .integer⟩]⟩ : FamilyTemplate))
      (.user 9 []) 0 = none ∧
    signature (fun _ => some (⟨[], [⟨.reference (.bound 0), .integer⟩]⟩ : FamilyTemplate))
      (.user 9 []) 0 = none := by decide

end Examples

end Ash.OneShot.DeclarationResults

#print axioms Ash.OneShot.DeclarationResults.named_parameters_open
#print axioms Ash.OneShot.DeclarationResults.named_parameters_frozen
#print axioms Ash.OneShot.DeclarationResults.name_bound_open
#print axioms Ash.OneShot.DeclarationResults.type_bound_open
#print axioms Ash.OneShot.DeclarationResults.name_bound_realizes
#print axioms Ash.OneShot.DeclarationResults.type_bound_realizes
#print axioms Ash.OneShot.DeclarationResults.operation_bound_open
#print axioms Ash.OneShot.DeclarationResults.mapM_frozen_effects
#print axioms Ash.OneShot.DeclarationResults.mapM_frozen_names
#print axioms Ash.OneShot.DeclarationResults.decode_frozen_type
#print axioms Ash.OneShot.DeclarationResults.decode_realized_type
#print axioms Ash.OneShot.DeclarationResults.declared_signature_known
#print axioms Ash.OneShot.DeclarationResults.declared_operation_bound
#print axioms Ash.OneShot.DeclarationResults.operation_bound_runtime
#print axioms Ash.OneShot.DeclarationResults.closed_argument_frozen
#print axioms Ash.OneShot.DeclarationResults.closed_arguments_frozen
#print axioms Ash.OneShot.DeclarationResults.closed_effect_frozen
#print axioms Ash.OneShot.DeclarationResults.closed_operation_bound_runtime
#print axioms Ash.OneShot.DeclarationResults.Examples.positional_aliases_preserved
#print axioms Ash.OneShot.DeclarationResults.Examples.wrong_arity_rejected
#print axioms Ash.OneShot.DeclarationResults.Examples.nonresource_argument_rejected
#print axioms Ash.OneShot.DeclarationResults.Examples.nested_resource_argument_rejected
#print axioms Ash.OneShot.DeclarationResults.Examples.invalid_declarations_rejected
#print axioms Ash.OneShot.DeclarationResults.Examples.unknown_family_and_operation_rejected
#print axioms Ash.OneShot.DeclarationResults.Examples.same_declaration_at_distinct_activations
#print axioms Ash.OneShot.DeclarationResults.Examples.builtins_ignore_user_registry

#print axioms Ash.OneShot.DeclarationResults.Examples.malformed_input_rejected_before_result_analysis
