import CorePayloadRefinement

/-! DN-0033 helper/branch generalization gate. Positive RawStep and selected
payload evidence is separate from old whole-expression source admission. The
obstructions concern only these unchanged Code terms and current constructors;
no impossibility of every translation or completed M4 repair is claimed. -/
namespace Ash.OneShot.CoreRefinementJoins
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Contracts Value Environment)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CorePayloadRefinement

variable {operations : Operations} {policy : Syntax.TicketPolicy} {contracts : Contracts}
  {ports : OperationRows operations} {owners : ContractRows contracts} {world : List Nat}

/-- Structural inversion preserves the lambda body's actual checking signature,
including unused bind structure. There is no equal-port coercion constructor. -/
theorem unit_lambda_shape
    (source : SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      (.lambda 2 .unit) value demand requirements checking) :
    ∃ input requests latent, value = .function input .unit requests latent SourcePlanSignatures.Signature.pure := by
  cases source with
  | lambda body => cases body; exact ⟨_, _, _, rfl⟩

theorem sequenced_lambda_shape
    (source : SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      (.lambda 2 (.bind 3 .unit .unit)) value demand requirements checking) :
    ∃ input requests latent, value = .function input .unit requests latent
      (.sequence SourcePlanSignatures.Signature.pure SourcePlanSignatures.Signature.pure) := by
  cases source with
  | lambda body => cases body with
    | bind initializer suffix => cases initializer; cases suffix; exact ⟨_, _, _, rfl⟩

theorem no_common_rich_value
    (first : SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      (.lambda 2 .unit) value firstDemand firstRequirements firstChecking)
    (second : SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      (.lambda 2 (.bind 3 .unit .unit)) value secondDemand secondRequirements secondChecking) : False := by
  obtain ⟨input, requests, latent, firstShape⟩ := unit_lambda_shape first
  obtain ⟨otherInput, otherRequests, otherLatent, secondShape⟩ := sequenced_lambda_shape second
  have erased := congrArg Value.erase (firstShape.symm.trans secondShape)
  have sameDependencies := (SourceDependencyAnnotations.Value.function.inj erased).2.2.2.2
  cases sameDependencies

theorem no_common_source_summaries (value : Value) :
    ¬ (SourcePlannedSources.ValueSummary operations policy contracts world environment allowed
        (.lambda 2 .unit) value ∧
      SourcePlannedSources.ValueSummary operations policy contracts world environment allowed
        (.lambda 2 (.bind 3 .unit .unit)) value) := by
  rintro ⟨first, second⟩
  exact no_common_rich_value first second

theorem homogeneous_branch_unavailable :
    ¬ SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      (.branch (.boolean choice) (.lambda 2 .unit) (.lambda 2 (.bind 3 .unit .unit)))
      value demand requirements checking := by
  intro source
  cases source with
  | branch condition yes no same => exact no_common_rich_value yes no

/-- One unchanged ordinary helper is specialized only in its proof annotations. -/
def helperCode : Code := .lambda 0 (.app (.variable 0) .unit)
def helperUse (payload : Payload operations policy contracts ports owners world) : Code :=
  .bind 4 helperCode (.app (.variable 4) payload.code)

theorem helper_closed : ClosedValue helperCode := by
  simp [helperCode, ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames,
    Code.dependencies, Syntax.without]

theorem helper_bind (payload : Payload operations policy contracts ports owners world) (tail : Stack) :
    RawStep ⟨helperUse payload, .none, tail⟩ ⟨.app helperCode payload.code, .none, tail⟩ [] [] := by
  have absent := ScopedTyping.closedValue_no_variable payload.closed (name := 4)
  have ready : ClosedExcept 4 (.app (.variable 4) payload.code) := by
    intro name present
    have split : name = 4 ∨ Syntax.Dependency.variable name ∈ payload.code.dependencies := by
      simpa [Code.dependencies] using present
    rcases split with same | captured
    · exact same
    · exact False.elim (ScopedTyping.closedValue_no_variable payload.closed captured)
  simpa only [helperUse, Code.subst, if_true,
    ScopedTyping.subst_absent payload.code 4 helperCode absent] using
      RawStep.bind 4 helperCode (.app (.variable 4) payload.code) .none tail helper_closed ready

theorem helper_beta (payload : Payload operations policy contracts ports owners world) (tail : Stack) :
    RawStep ⟨.app helperCode payload.code, .none, tail⟩
      ⟨.app payload.code .unit, .none, tail⟩ [] [] := by
  simpa only [helperCode, Code.subst, if_true] using
    RawStep.beta 0 (.app (.variable 0) .unit) payload.code .none tail payload.closed helper_closed

/-- Each helper call reaches the actual payload body with its supplied static
Source/Auth proof. The proof uses no successful-execution or successor premise. -/
theorem helper_invocation (payload : Payload operations policy contracts ports owners world) (tail : Stack) :
    RawStep ⟨helperUse payload, .none, tail⟩ ⟨.app helperCode payload.code, .none, tail⟩ [] [] ∧
    RawStep ⟨.app helperCode payload.code, .none, tail⟩ ⟨.app payload.code .unit, .none, tail⟩ [] [] ∧
    RawStep ⟨.app payload.code .unit, .none, tail⟩ ⟨payload.body.subst 2 .unit, .none, tail⟩ [] [] ∧
    (∃ source : SourcePlannedSources.Expression operations policy contracts world [] .none
        (fun _ => none) (payload.body.subst 2 .unit) .unit [] payload.requirements (signature payload.plan),
      Auth operations policy ports owners baseRows source .unit payload.rows) ∧
    Syntax.resourceDependencies (payload.body.subst 2 .unit).dependencies ⊆ payload.retained :=
  ⟨helper_bind payload tail, helper_beta payload tail, payload.beta _ _,
    payload.invocation, beta_support payload⟩

/-- This runtime branch chooses an actual payload refinement, rather than
claiming one homogeneous rich value for both syntactic arms. -/
def branchCode (choice : Bool) (left right : Payload operations policy contracts ports owners world) : Code :=
  .branch (.boolean choice) left.code right.code
def selectedPayload (choice : Bool) (left right : Payload operations policy contracts ports owners world) :
    Payload operations policy contracts ports owners world := if choice then left else right

theorem branch_step (left right : Payload operations policy contracts ports owners world) (choice : Bool) (tail : Stack) :
    RawStep ⟨branchCode choice left right, .none, tail⟩
      ⟨(selectedPayload choice left right).code, .none, tail⟩ [] [] := by
  cases choice
  · exact .ifFalse _ _ _ _
  · exact .ifTrue _ _ _ _

theorem branch_selected_port (left right : Payload operations policy contracts ports owners world) (choice : Bool) :
    (selectedPayload choice left right).value.erase.erase.port = ScopedPorts.Port.function .unit .unit [] :=
  Payload.exact_port _

theorem branch_selected_support (left right : Payload operations policy contracts ports owners world) (choice : Bool) :
    (selectedPayload choice left right).retained = if choice then left.retained else right.retained := by
  cases choice <;> rfl

theorem branch_selected_source (left right : Payload operations policy contracts ports owners world) (choice : Bool) :
    SourcePlannedSources.ValueSummary operations policy contracts world (fun _ => none) []
      (selectedPayload choice left right).code (selectedPayload choice left right).value :=
  Payload.closure_source _

/-- A stored helper at one environment entry has one old rich argument type.
Both calls cannot be admitted by the existing exact-input app constructor. -/
theorem fixed_helper_input_unavailable
    (first : SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      (.app (.variable 4) (.lambda 2 .unit)) firstValue firstDemand firstRequirements firstChecking)
    (second : SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      (.app (.variable 4) (.lambda 2 (.bind 3 .unit .unit))) secondValue secondDemand secondRequirements secondChecking) :
    False := by
  cases first with
  | app function argument => cases function with
    | «variable» known =>
      cases second with
      | app otherFunction otherArgument => cases otherFunction with
        | «variable» otherKnown =>
          have sameHelper := Option.some.inj (known.symm.trans otherKnown)
          have sameInput := (Value.function.inj sameHelper).1
          exact no_common_rich_value argument (sameInput.symm ▸ otherArgument)

/-- The identical helper Code and tail produce Unit for both specializations.
These traces reuse the existing RawTrace ledger, with no creations/completions. -/
theorem trivial_helper_trace (tail : Stack) :
    let payload : Payload operations policy contracts ports owners world := trivial
    RawTrace ⟨helperUse payload, .none, tail⟩ ⟨.unit, .none, tail⟩ [] [] :=
  .next (helper_bind _ tail) (.next (helper_beta _ tail)
    (.next (Payload.beta _ _ _) (.refl _)))

theorem sequenced_helper_trace (tail : Stack) :
    let payload : Payload operations policy contracts ports owners world := sequenced
    RawTrace ⟨helperUse payload, .none, tail⟩ ⟨.unit, .none, tail⟩ [] [] :=
  .next (helper_bind _ tail) (.next (helper_beta _ tail)
    (.next (Payload.beta _ _ _) (.next (sequenced_body_step tail) (.refl _))))

theorem retaining_branch_support (issued : identity ∈ world) (choice : Bool) :
    let left : Payload operations policy contracts ports owners world := trivial
    let right : Payload operations policy contracts ports owners world := retaining identity issued
    (selectedPayload choice left right).retained = if choice then [] else [identity] := by
  cases choice
  · exact retaining_support issued
  · rfl

theorem retaining_branch_inner_receiver (issued : identity ∈ world) (choice : Bool) :
    let left : Payload operations policy contracts ports owners world := trivial
    let right : Payload operations policy contracts ports owners world := retaining identity issued
    let selected := selectedPayload choice left right
    checkReceiver selected (innerScope selected identity) [] = true := by
  cases choice
  · exact retaining_receiver_checked issued
  · exact trivial_receiver

/-- The actual outside-owner receiver accepts the resource-free arm and rejects
precisely the retaining arm; its requirement is not erased by the common port. -/
theorem retaining_branch_outer_receiver (issued : identity ∈ world) (choice : Bool) :
    let left : Payload operations policy contracts ports owners world := trivial
    let right : Payload operations policy contracts ports owners world := retaining identity issued
    let selected := selectedPayload choice left right
    checkReceiver selected (outerScope selected identity) [] = choice := by
  cases choice
  · exact retaining_receiver_rejected issued
  · simp [selectedPayload, checkReceiver, SourceDependencyCapture.select, outerScope, invoke,
      table, families, SourceDependencyCapture.lookupDependencies, SourceDependencyCapture.Selection.prepend, lookup,
      Payload.retained, Payload.code, CorePayloadRefinement.trivial, Code.dependencies, Syntax.without, ScopedPorts.Support.evaluate]

/- This gate retains positive helper/branch operational and per-specialization
body Source/Auth/port/support evidence. It also proves current exact-input and
homogeneous-result source constructors cannot admit the unchanged two-body
examples. No common authenticated whole-expression Source, callable input/result
family, heterogeneous branch join, or M4 InitialAdmission is constructed.

The payload-family candidate must generalize ordinary callable parameters and
results, branch joins, higher-order operation outputs and continuation/bind
refinements, as well as operation operands. A different justified translation
remains possible; these inversions alone do not select a general interface or
exclude any required higher-order Core cases. -/

#print axioms fixed_helper_input_unavailable
#print axioms trivial_helper_trace
#print axioms sequenced_helper_trace
#print axioms retaining_branch_support
#print axioms retaining_branch_inner_receiver
#print axioms retaining_branch_outer_receiver

#print axioms no_common_rich_value
#print axioms homogeneous_branch_unavailable
#print axioms helper_invocation
#print axioms branch_step
#print axioms branch_selected_support
end Ash.OneShot.CoreRefinementJoins
