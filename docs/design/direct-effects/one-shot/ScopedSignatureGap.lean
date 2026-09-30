import ScopedRetirement

/-!
A source correspondence obstruction in the current annotated typing model.
Globally fixed operation ports also fix their retained-resource annotations.
Generative checking then excludes a callable payload retaining a locally
allocated resource, even when that resource remains outside the handler cut.
This is a model limitation, not evidence for restricting current Core.
-/

namespace Ash.OneShot.ScopedSignatureGap
open Syntax Instantiation ScopedExpressions ScopedExecution ScopedTyping
open Typing (Signature TypeEnv)

/-- Two distinct openings cannot justify a fixed port's private support. -/
theorem two_openings_confine_support {support world : List Nat}
    (left : support ⊆ world ++ [first]) (right : support ⊆ world ++ [second])
    (different : first ≠ second) : support ⊆ world := by
  intro identity retained
  rcases List.mem_append.mp (left retained) with old | current
  · exact old
  · have same := List.mem_singleton.mp current
    rcases List.mem_append.mp (right retained) with old | other
    · exact old
    · exact False.elim (different (same.symm.trans (List.mem_singleton.mp other)))

/-- Universal fresh checking confines any fixed support to the old world. -/
theorem all_openings_confine_support {support world : List Nat}
    (opened : ∀ identity, identity ∉ world → support ⊆ world ++ [identity]) :
    support ⊆ world := by
  obtain ⟨first, freshFirst⟩ := fresh_world_name world
  obtain ⟨second, freshSecond⟩ := fresh_world_name (world ++ [first])
  apply two_openings_confine_support (opened first freshFirst)
    (opened second (fun old => freshSecond (List.mem_append_left _ old)))
  intro same
  exact freshSecond (List.mem_append_right _ (by simp [same]))

/-- Port support follows from actual operand typing, even before it is a value. -/
theorem request_ports_in_world
    (typed : Typed signature world environment ticket allowed
      (.perform (freezeEffect requested) operation operand) output)
    (known : signature requested operation = some (input, output)) :
    InWorld world input ∧ InWorld world output := by
  obtain ⟨actual, lookup, available, operandTyped⟩ := typed_perform_inversion typed
  have same := Option.some.inj (lookup.symm.trans known)
  cases same
  exact ⟨typed_result_in_world operandTyped, typed_result_in_world typed⟩

/-- This confines fixed annotations, not the independently inferred support of
    differently instantiated callable values. That distinction is the gap. -/
theorem generative_request_ports_confined
    {environments : Nat → TypeEnv} {tickets : Nat → Typing.TicketType}
    {allowed : Nat → List Instance} {operands : Nat → Code}
    (known : signature requested operation = some (input, output))
    (opened : ∀ identity, identity ∉ world →
      Typed signature (world ++ [identity]) (environments identity) (tickets identity)
        (allowed identity) (.perform (freezeEffect requested) operation (operands identity)) output) :
    InWorld world input ∧ InWorld world output := by
  constructor
  · exact all_openings_confine_support (fun identity fresh =>
      (request_ports_in_world (opened identity fresh) known).1)
  · exact all_openings_confine_support (fun identity fresh =>
      (request_ports_in_world (opened identity fresh) known).2)

namespace Examples

def send : Instance := .user 1 []
def payload (name : ResourceName) : Code :=
  .lambda 2 (.bind 3 (.resourceRef name) (.integer 42))
def clauses : ScopedExpressions.Clauses := .cons 0 5 9 (.resume 9 .unit) .nil
def body : Code := .handle (freezeEffect send)
  (.perform (freezeEffect send) 0 (payload (.bound 4))) clauses
def program : Code := .resource 4 (.integer 41) body
def openedBody (identity : Nat) : Code := .handle (freezeEffect send)
  (.perform (freezeEffect send) 0 (payload (.activation identity))) clauses

theorem body_opening (identity : Nat) :
    body.instantiate (Environment.empty.bind 4 identity) = openedBody identity := by
  rfl

theorem opened_payload_retains (identity : Nat) :
    identity ∈ resourceDependencies (payload (.activation identity)).dependencies := by
  simp [payload, Code.dependencies, without, resourceDependencies]

theorem opened_payload_is_value (identity : Nat) :
    (payload (.activation identity)).IsValue := by trivial

theorem opened_request_port
    (typed : Typed signature world environment ticket allowed (openedBody identity) answer) :
    ∃ input output, signature send 0 = some (input, output) ∧
      InWorld world input ∧ identity ∈ input.resources := by
  unfold openedBody at typed
  generalize handlerEq : freezeEffect send = handlerEffect at typed
  cases typed with
  | handle request handler coverage unique residual =>
      have same := freeze_effect_injective handlerEq
      cases same
      obtain ⟨input, known, available, operand⟩ := typed_perform_inversion request
      exact ⟨input, _, known, typed_result_in_world operand,
        typed_value_support operand (opened_payload_is_value identity) (opened_payload_retains identity)⟩

/-- No fixed signature, result type or effect bound can type this closed source
    in the present model. The same exact Send instance occurs at both openings. -/
theorem safe_source_has_no_fixed_signature_typing
    (signature : Signature) (answer : Ty) (allowed : List Instance) :
    ¬ Typed signature [] TypeEnv.empty .none allowed program answer := by
  intro typed
  cases typed with
  | resource initializer opened resultBound effectsBound effects =>
      have zero := opened 0 (by simp)
      have one := opened 1 (by simp)
      rw [body_opening] at zero one
      obtain ⟨inputZero, outputZero, knownZero, boundZero, retainedZero⟩ := opened_request_port zero
      obtain ⟨inputOne, outputOne, knownOne, boundOne, retainedOne⟩ := opened_request_port one
      have same := Option.some.inj (knownZero.symm.trans knownOne)
      cases same
      have confined := two_openings_confine_support boundZero boundOne (by decide : 0 ≠ 1)
      exact List.not_mem_nil (confined retainedZero)

theorem program_resource_closed : program.ResourceClosed := by
  simp [program, body, payload, clauses, send, Code.ResourceClosed, Code.freeNames,
    ScopedExpressions.Clauses.freeNames, ResourceName.freeNames, freezeEffect, Effect.freeNames]

theorem program_has_no_initial_resource_atoms : resourceDependencies program.dependencies = [] := by
  simp [program, body, payload, clauses, send, Code.dependencies,
    ScopedExpressions.Clauses.dependencies, effectAtoms, freezeEffect, Effect.resources,
    without, resourceDependencies]

theorem program_uses_one_shot :
    ScopedExpressions.Uses (fun _ => ActionRequirements.resumeOnly) .none .available program .available :=
  .resource .integer (.handle (.perform (.lambda (.bind .resourceRef .integer)))
    (.cons (.resume rfl .unit) .nil))

def handler : HandlerData := ⟨8, send, clauses, .none, .unit, by
  simp [clauses, ScopedExpressions.Clauses.dependencies, Code.dependencies, without, ticketDependencies]⟩
def outside : Stack := .push (.cell 0 41 .none .unit) .nil
def capture : Stack := .push (.handler handler) .nil

theorem payload_closed : ClosedValue (payload (.activation 0)) := by
  simp [ScopedExpressions.ClosedValue, payload, Code.IsValue, Code.ResourceClosed, Code.freeNames,
    ResourceName.freeNames, Code.dependencies, without]

/-- The retained resource is outside the exact selected cut, and the payload
    is supported there. Rejecting this source cannot be justified by that cut. -/
theorem actual_boundary_supports_payload :
    HandlerCut send (.push (.handler handler) outside) capture outside handler ∧
    resourceDependencies (payload (.activation 0)).dependencies ⊆ outside.erase.visible ∧
    Owner.resource 0 ∉ capture.erase.owners := by
  refine ⟨.hit handler outside rfl, ?_, ?_⟩
  · simp [payload, Code.dependencies, without, resourceDependencies, outside,
      Stack.erase, ExecFrame.erase, Control.visible, Frame.visible]
  · simp [capture, Stack.erase, ExecFrame.erase, HandlerData.erase, Control.owners, Frame.owners, handler]

/-- The raw machine represents the source and completes both owners. This is
    an operational witness, not a repaired source typing derivation. -/
theorem source_executes :
    RawTrace ⟨program, .none, .nil⟩ ⟨.unit, .none, .nil⟩
      [.resource 0, .ticket 7] [.resource 0, .ticket 7] := by
  have unitClosed : ClosedValue Code.unit := by
    simp [ScopedExpressions.ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames, Code.dependencies]
  have entry := RawStep.enterCell 4 0 41 body .none .unit .nil program_resource_closed
  have install := RawStep.enterHandler handler
    (.perform (freezeEffect send) 0 (payload (.activation 0))) outside
  have request := RawStep.capture send 0 5 9 7 (payload (.activation 0)) (.resume 9 .unit)
    .none (.push (.handler handler) outside) capture outside handler .unit
    actual_boundary_supports_payload.1 .hit payload_closed
    (by intro name member; simp [Code.dependencies] at member)
  have resume := RawStep.resume 9 7 (.ticket 9 7) .none .unit .unit .nil capture outside
    .unit unitClosed rfl
  have leave := RawStep.leaveHandler handler .unit unitClosed (.ticket 9 7)
    (.spent 7 .unit .none outside)
  have finish := RawStep.leaveClause 7 .unit .unit unitClosed .none .none outside
  have release := RawStep.leaveCell 0 41 .unit .none .none .unit unitClosed .nil
  exact .next entry (.next install (.next request (.next resume (.next leave (.next finish (.next release (.refl _)))))))

theorem source_execution_has_fresh_owners :
    RunSteps ⟨⟨program, .none, .nil⟩, [], []⟩
      ⟨⟨.unit, .none, .nil⟩, [.resource 0, .ticket 7], [.resource 0, .ticket 7]⟩ :=
  raw_trace_enacts source_executes (by decide)

end Examples
end Ash.OneShot.ScopedSignatureGap

#print axioms Ash.OneShot.ScopedSignatureGap.two_openings_confine_support
#print axioms Ash.OneShot.ScopedSignatureGap.all_openings_confine_support
#print axioms Ash.OneShot.ScopedSignatureGap.request_ports_in_world
#print axioms Ash.OneShot.ScopedSignatureGap.generative_request_ports_confined
#print axioms Ash.OneShot.ScopedSignatureGap.Examples.body_opening
#print axioms Ash.OneShot.ScopedSignatureGap.Examples.opened_payload_retains
#print axioms Ash.OneShot.ScopedSignatureGap.Examples.opened_payload_is_value
#print axioms Ash.OneShot.ScopedSignatureGap.Examples.opened_request_port
#print axioms Ash.OneShot.ScopedSignatureGap.Examples.safe_source_has_no_fixed_signature_typing
#print axioms Ash.OneShot.ScopedSignatureGap.Examples.program_resource_closed
#print axioms Ash.OneShot.ScopedSignatureGap.Examples.program_has_no_initial_resource_atoms
#print axioms Ash.OneShot.ScopedSignatureGap.Examples.program_uses_one_shot
#print axioms Ash.OneShot.ScopedSignatureGap.Examples.payload_closed
#print axioms Ash.OneShot.ScopedSignatureGap.Examples.actual_boundary_supports_payload
#print axioms Ash.OneShot.ScopedSignatureGap.Examples.source_executes
#print axioms Ash.OneShot.ScopedSignatureGap.Examples.source_execution_has_fresh_owners
