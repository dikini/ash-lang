import SourceScheduledRetainedRuns

/-! A source derivation retains binding type choices that raw code, result
ports and plan signatures do not determine. Finite source hints reuse lexical
type realization to authenticate ports and prevent resource-name rebinding.
Threading these hints through the source and execution judgments is still open.
The gap is annotation provenance, not a stuck execution or impossible inference. -/

namespace Ash.OneShot.SourceFocusHints
open Instantiation ScopedExecution
open SourceScheduledExecution (stackInputPort)

/-- A lexical source type annotation supplies the operand port. Existing
instantiation freezes its resource names before it moves with runtime code. -/
def inputPort (environment : Environment) (hint : ValueType) : Option ScopedPorts.Port :=
  (DeclarationResults.decodeType (hint.instantiate environment)).map ScopedPorts.eraseType

/-- Static source checking authenticates the hint against the chosen rich
source type. Retaining that hint through execution is a separate obligation. -/
def checkSource (environment : Environment) (hint : ValueType) (value : SourcePlannedTyping.Value) : Bool :=
  decide (inputPort environment hint = some value.erase.erase.port)

theorem check_source_iff : checkSource environment hint value = true ↔
    inputPort environment hint = some value.erase.erase.port := by
  simp [checkSource]

theorem source_port_unique
    (first : checkSource environment hint a = true)
    (second : checkSource environment hint b = true) : a.erase.erase.port = b.erase.erase.port :=
  Option.some.inj ((check_source_iff.mp first).symm.trans (check_source_iff.mp second))

def checkFrame (environment : Environment) (hint : ValueType) (result : ScopedPorts.Port)
    (stack : Stack) (plain : PlainData) : Bool :=
  decide (inputPort environment hint = some (ScopedPorts.eraseType plain.input) ∧
    ScopedPorts.eraseType plain.output = stackInputPort stack result)

theorem input_port_realized (realized : TypeRealizes environment hint type) :
    inputPort environment hint = some (ScopedPorts.eraseType type) := by
  simp only [inputPort, DeclarationResults.decode_realized_type realized, Option.map_some]

/-- Given the source annotation's realization, the executable guard is exactly
port agreement. This supplies no code typing or one-shot permission. -/
theorem check_frame_iff (realized : TypeRealizes environment hint type) :
    checkFrame environment hint result stack plain = true ↔
      ScopedPorts.eraseType plain.input = ScopedPorts.eraseType type ∧
      ScopedPorts.eraseType plain.output = stackInputPort stack result := by
  unfold checkFrame
  rw [input_port_realized realized]
  simp only [decide_eq_true_eq, Option.some.injEq]
  exact and_congr eq_comm Iff.rfl

/-- The source check and runtime guard refer to the same finite hint. Their
agreement derives frame ports, without adding a source-state proof to a trace. -/
theorem source_frame_agreement
    (source : checkSource environment hint value = true)
    (frame : checkFrame environment hint result stack plain = true) :
    ScopedPorts.eraseType plain.input = value.erase.erase.port ∧
    ScopedPorts.eraseType plain.output = stackInputPort stack result := by
  have checked := of_decide_eq_true frame
  exact ⟨Option.some.inj (checked.1.symm.trans (check_source_iff.mp source)), checked.2⟩

/-- Reuse the established lexical-freezing theorem. Moving an already
realized hint under a later resource environment cannot change its port. -/
theorem realized_hint_retained (realized : TypeRealizes environment hint type)
    (later : Environment) :
    inputPort later (hint.instantiate environment) = inputPort environment hint := by
  rw [input_port_realized realized]
  simp only [inputPort, realized_type_cannot_be_rebound realized,
    DeclarationResults.decode_frozen_type, Option.map_some]

theorem frame_check_retained (realized : TypeRealizes environment hint type)
    (later : Environment) :
    checkFrame later (hint.instantiate environment) result stack plain =
      checkFrame environment hint result stack plain := by
  simp only [checkFrame, realized_hint_retained realized]

end Ash.OneShot.SourceFocusHints

namespace Ash.OneShot.SourceFocusAnnotationGap
open ScopedExpressions ScopedExecution
open SourcePlannedTyping (Value)
open SourcePlannedSources (Expression Context)
open SourceScheduledExecution
variable {input : Value}

abbrev empty : RecursiveRequirements.Requirements [] := .request [] []
def constant : Code := .lambda 2 .unit
def initializer : Code := .bind 1 .unit constant
def program : Code := .bind 0 initializer .unit
def functionType (input : Value) : Value := .function input .unit [] [] .pure
def requirements : RecursiveRequirements.Requirements [] := .sequence (.sequence empty empty) empty
def plan : SourceDeclarationPlans.Plan (.sequence (.sequence .pure .pure) .pure) :=
  .sequence (.sequence .pure .pure) .pure

theorem constant_source (formed : ScopedPorts.InWorld [] input.erase.erase.port) :
    Expression operations policy (fun _ => none) [] [] .none environment constant
      (functionType input) [] empty .pure := by
  refine .lambda .unit (RecursiveOutward.Outward.request (layers := [])) ?_ (by simp)
  simpa [ScopedPorts.InWorld, CoherentSourceTypes.Value.port, ScopedPorts.Port.resources,
    SourcePlannedTyping.Value.erase, SourceDependencyAnnotations.Value.erase] using formed

theorem initializer_source (formed : ScopedPorts.InWorld [] input.erase.erase.port) :
    Expression operations policy (fun _ => none) [] [] .none environment initializer
      (functionType input) [] (.sequence empty empty) (.sequence .pure .pure) :=
  .bind .unit (constant_source formed)

/-- Changing the unused lambda parameter's type changes neither the initial
program's result type nor its source requirement and plan signatures. -/
theorem program_source (formed : ScopedPorts.InWorld [] input.erase.erase.port) :
    Expression operations policy (fun _ => none) [] [] .none (fun _ => none) program
      .unit [] requirements (SourcePlanSignatures.signature plan) :=
  .bind (initializer_source formed) .unit

/-- These are the actual child and context judgments used by the existing
focus decomposition, not arbitrary annotations on a raw frame. -/
def BindingChoice (input : Value) : Prop :=
  Expression InitialAdmissionExamples.operations (fun _ => ⟨true, true⟩) (fun _ => none)
    [] [] .none (fun _ => none) initializer input [] (.sequence empty empty) (.sequence .pure .pure) ∧
  Context InitialAdmissionExamples.operations (fun _ => ⟨true, true⟩) (fun _ => none)
    [] (fun _ => none) [] .none (.bind 0 .unit) input .unit [] empty .pure

theorem unit_choice : BindingChoice (functionType .unit) :=
  ⟨initializer_source (by simp [ScopedPorts.InWorld, ScopedPorts.Port.resources,
    SourcePlannedTyping.Value.erase, SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port]), .bind .unit⟩

theorem integer_choice : BindingChoice (functionType .integer) :=
  ⟨initializer_source (by simp [ScopedPorts.InWorld, ScopedPorts.Port.resources,
    SourcePlannedTyping.Value.erase, SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port]), .bind .unit⟩

theorem actual_focus : Focus program initializer (.bind 0 .unit) :=
  .bind (by simp [initializer, Code.IsValue])

/-- No single port, even for this fixed code/result/plan, agrees with every
admitted typing choice. Canonical inference would be a new admission rule. -/
theorem no_unique_binding_port :
    ¬ ∃ port : ScopedPorts.Port, ∀ input, BindingChoice input → port = input.erase.erase.port := by
  rintro ⟨port, unique⟩
  have conflict := (unique _ unit_choice).symm.trans (unique _ integer_choice)
  cases conflict

/-- Ordinary scheduling accepts both source derivations' identical plan. -/
theorem scheduled : SourceScheduledChecks.Local [] (fun _ => none) (OwnerPhaseTransitions.available []) [] plan .nil :=
  .sequence (.sequence .pure .pure) .pure

theorem admitted : checkInitial program requirements = true := by
  simp [checkInitial, requirements, empty,
    RecursiveRequirements.evaluate, RecursiveRequirements.evaluateFuel, OwnerSource.exportAt,
    OwnerPhaseTransitions.project, ProtectionResiduals.residualize, ProtectionResiduals.merge,
    OwnerPhaseTransitions.spendAll, ProtectionContracts.checkFootprint, program, initializer, constant,
    Code.dependencies, Syntax.without, Syntax.resourceDependencies]

theorem completion : CompletionContracts.Derives (fun _ => none) CallableContracts.Environment.empty [] .none
    program (.storage []) := by
  exact .bind (input := .function [] (.storage []) (.storage []))
    (.bind (input := .storage []) (.leaf trivial rfl .nil)
      (.lambda (.leaf trivial rfl .nil) .nil)) (.leaf trivial rfl .nil)

/-- The ambiguity occurs at the existing initial-admission boundary, not only
in a weaker isolated port-typing relation. Each choice establishes the full Run. -/
theorem initial_run_with_choice
    (formed : ScopedPorts.InWorld [] input.erase.erase.port) :
    Run InitialAdmissionExamples.operations (fun _ => none) policy (fun _ => none) (fun _ => none)
      tables families required (fun _ => none) ⟨⟨⟨program, .none, .nil⟩, [], []⟩, []⟩
      .nil .unit [] [] (.storage []) :=
  (initial_run (plan := plan) (program_source formed) scheduled admitted completion
    InitialAdmissionExamples.signature_agreement).2


/-- Both admissible source choices have finite explicit hints. These hints are
data; their connection to the initial source judgment must be retained. -/
def unitHint : Instantiation.ValueType := .function .unit .unit [] []
def integerHint : Instantiation.ValueType := .function .integer .unit [] []
def bindingFrame (input : Ty) : PlainData := ⟨.bind 0 .unit, .none, input, .unit, [], rfl⟩

theorem explicit_choices_checked :
    SourceFocusHints.checkFrame Instantiation.Environment.empty unitHint .unit .nil
      (bindingFrame (.function .unit .unit [] [])) = true ∧
    SourceFocusHints.checkFrame Instantiation.Environment.empty integerHint .unit .nil
      (bindingFrame (.function .integer .unit [] [])) = true := by decide

theorem source_choices_authenticated :
    SourceFocusHints.checkSource Instantiation.Environment.empty unitHint (functionType .unit) = true ∧
    SourceFocusHints.checkSource Instantiation.Environment.empty integerHint (functionType .integer) = true ∧
    SourceFocusHints.checkSource Instantiation.Environment.empty unitHint (functionType .integer) = false ∧
    SourceFocusHints.checkSource Instantiation.Environment.empty integerHint (functionType .unit) = false := by decide

theorem changing_choice_rejected :
    SourceFocusHints.checkFrame Instantiation.Environment.empty unitHint .unit .nil
      (bindingFrame (.function .integer .unit [] [])) = false ∧
    SourceFocusHints.checkFrame Instantiation.Environment.empty integerHint .unit .nil
      (bindingFrame (.function .unit .unit [] [])) = false := by decide

theorem unresolved_resource_rejected :
    SourceFocusHints.inputPort Instantiation.Environment.empty (.reference (.bound 7)) = none := by decide

/-- Once opened, a resource-bearing hint retains its first activation even
under a later environment binding the same source name differently. -/
theorem opened_hint_keeps_identity :
    SourceFocusHints.inputPort (Instantiation.Environment.empty.bind 7 29)
      ((Instantiation.ValueType.reference (.bound 7)).instantiate
        (Instantiation.Environment.empty.bind 7 11)) = some (.reference 11) := by decide

end Ash.OneShot.SourceFocusAnnotationGap

#print axioms Ash.OneShot.SourceFocusAnnotationGap.constant_source
#print axioms Ash.OneShot.SourceFocusAnnotationGap.initializer_source
#print axioms Ash.OneShot.SourceFocusAnnotationGap.program_source
#print axioms Ash.OneShot.SourceFocusAnnotationGap.unit_choice
#print axioms Ash.OneShot.SourceFocusAnnotationGap.integer_choice
#print axioms Ash.OneShot.SourceFocusAnnotationGap.actual_focus
#print axioms Ash.OneShot.SourceFocusAnnotationGap.no_unique_binding_port
#print axioms Ash.OneShot.SourceFocusAnnotationGap.scheduled
#print axioms Ash.OneShot.SourceFocusAnnotationGap.admitted
#print axioms Ash.OneShot.SourceFocusAnnotationGap.completion
#print axioms Ash.OneShot.SourceFocusAnnotationGap.initial_run_with_choice

#print axioms Ash.OneShot.SourceFocusHints.input_port_realized
#print axioms Ash.OneShot.SourceFocusHints.check_frame_iff
#print axioms Ash.OneShot.SourceFocusHints.realized_hint_retained
#print axioms Ash.OneShot.SourceFocusHints.frame_check_retained
#print axioms Ash.OneShot.SourceFocusHints.check_source_iff
#print axioms Ash.OneShot.SourceFocusHints.source_port_unique
#print axioms Ash.OneShot.SourceFocusHints.source_frame_agreement
#print axioms Ash.OneShot.SourceFocusAnnotationGap.explicit_choices_checked
#print axioms Ash.OneShot.SourceFocusAnnotationGap.changing_choice_rejected
#print axioms Ash.OneShot.SourceFocusAnnotationGap.unresolved_resource_rejected
#print axioms Ash.OneShot.SourceFocusAnnotationGap.opened_hint_keeps_identity
#print axioms Ash.OneShot.SourceFocusAnnotationGap.source_choices_authenticated
