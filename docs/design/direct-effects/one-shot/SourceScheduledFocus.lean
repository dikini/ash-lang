import SourceScheduledState
import SourcePlannedFocus

/-! Focusing retains the exact child and pending-context plans. The full
scheduled state is reconstructed using the established source decomposition,
frame preparation, row reassociation and saved-capture transport proofs. -/
namespace Ash.OneShot.SourceScheduledFocus
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements evaluate)
open ProtectionResiduals (merge)
open OwnerPhaseTransitions (spendAll)
open SourceDependencyAnnotations (Dependencies)
open SourcePlannedTyping (Value)
open SourcePlannedSources (Expression Context FocusSignature focus_decompose)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (Signature signature)
open SourceContextualHints (Hints)
open SourceScheduledChecks (Local Pending)
open SourceRetainedPlans (Forest)

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

/-- The signature split selects actual plan witnesses from the original
check, retaining all clause annotations. It assumes no new child check. -/
theorem signature_checks {whole : Signature wholeDependencies}
    {child : Signature childDependencies} {rest : Signature restDependencies}
    (split : FocusSignature whole child rest) {plan : Plan wholeDependencies} {hints : Hints receiving} {forest : Forest hints}
    (same : signature plan = whole) (checked : Local outward actions phases world plan forest) :
    ∃ childPlan : Plan childDependencies, ∃ restPlan : Plan restDependencies,
      signature childPlan = child ∧ signature restPlan = rest ∧
      Local outward actions phases world childPlan (.plain restPlan forest) ∧
      Local outward actions phases world restPlan forest := by
  cases split with
  | pure => cases plan; exact ⟨.pure, .pure, rfl, rfl, .pure, .pure⟩
  | sequence => cases plan with
    | sequence first second =>
        obtain ⟨firstSame, secondSame⟩ := Signature.sequence.inj same
        cases checked with
        | sequence firstCheck secondCheck => exact ⟨first, second, firstSame, secondSame, firstCheck, secondCheck⟩
  | pairRight => cases plan with
    | sequence first second =>
        obtain ⟨firstSame, secondSame⟩ := Signature.sequence.inj same
        cases checked with
        | sequence firstCheck secondCheck =>
            exact ⟨second, .pure, secondSame, rfl,
              SourceScheduledNeutralChecks.local_transport secondCheck (.extra .refl), .pure⟩
  | appArgument => cases plan with
    | sequence first remaining => cases remaining with
      | sequence argument body =>
          obtain ⟨firstSame, remainingSame⟩ := Signature.sequence.inj same
          obtain ⟨argumentSame, bodySame⟩ := Signature.sequence.inj remainingSame
          cases checked with
          | sequence firstCheck remainingCheck => cases remainingCheck with
            | sequence argumentCheck bodyCheck => exact ⟨argument, body, argumentSame, bodySame, argumentCheck, bodyCheck⟩

/-- All source Focus rules preserve the stronger local checks at the actual
child and saved-context scopes, with the same refined intermediate type. -/
theorem focus_checked {plan : Plan dependencies} {hints : Hints receiving} {forest : Forest hints}
    (source : Expression operations policy contracts world allowed scope environment whole output demand requirements (signature plan))
    (checked : Local outward actions phases world plan forest)
    (focus : Focus whole child position) :
    ∃ (input : Value) (childDemand restDemand : List Nat) (current : Requirements childDemand) (rest : Requirements restDemand)
      (childDependencies restDependencies : Dependencies) (childPlan : Plan childDependencies) (restPlan : Plan restDependencies),
      Expression operations policy contracts world allowed scope environment child input childDemand current (signature childPlan) ∧
      Context operations policy contracts world environment allowed scope position input output restDemand rest (signature restPlan) ∧
      Local outward actions phases world childPlan (.plain restPlan forest) ∧
      Local outward actions phases world restPlan forest ∧
      demand = childDemand ++ restDemand ∧
      ∀ store receiving before, evaluate store receiving before requirements =
        merge (evaluate store receiving before current) (evaluate store receiving (spendAll before childDemand) rest) := by
  obtain ⟨input, childDemand, restDemand, current, rest, childDependencies, restDependencies, childSignature, restSignature,
    childSource, context, split, sameDemand, evaluation⟩ := focus_decompose source focus
  obtain ⟨childPlan, restPlan, childSame, restSame, childCheck, restCheck⟩ := signature_checks split rfl checked
  exact ⟨input, childDemand, restDemand, current, rest, childDependencies, restDependencies, childPlan, restPlan,
    by simpa only [childSame] using childSource,
    by simpa only [restSame] using context,
    childCheck, restCheck, sameDemand, evaluation⟩

/-- Source focusing determines two erased port annotations. Every supplied
frame with that context, scope and those ports preserves the shared state.
The guard compares finite data and contains no successor-checking premise. -/
theorem focus_annotations
    (state : SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
      scope whole stack forest output demand row evidence)
    (position : Focus whole child context) :
    ∃ (plain : PlainData) (restDependencies : Dependencies) (restPlan : Plan restDependencies),
      plain.context = context ∧ plain.scope = scope ∧
      ∀ supplied : PlainData,
        supplied.context = context → supplied.scope = scope →
        ScopedPorts.eraseType supplied.input = ScopedPorts.eraseType plain.input →
        ScopedPorts.eraseType supplied.output = ScopedPorts.eraseType plain.output →
        RawStep ⟨whole, scope, stack⟩ ⟨child, scope, .push (.plain supplied) stack⟩ [] [] ∧
        SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
          scope child (.push (.plain supplied) stack) (.plain restPlan forest) output demand row evidence := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique checked accepted accounting =>
      obtain ⟨input, childDemand, restDemand, currentReq, restReq, childDependencies, restDependencies, childPlan, restPlan,
        childSource, sourceContext, childCheck, restCheck, sameDemand, evaluation⟩ := focus_checked current contextual position
      obtain ⟨plain, contextSame, scopeSame, inputAnnotation, outputAnnotation⟩ :=
        RecursiveContexts.prepare_plain (DeclaredSources.expression_erase
          (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase current))) position scopeTyped input.erase.erase
      refine ⟨plain, restDependencies, restPlan, contextSame, scopeSame, ?_⟩
      intro supplied suppliedContext suppliedScope suppliedInput suppliedOutput
      have inputSame := inputAnnotation.trans suppliedInput.symm
      have outputSame := outputAnnotation.trans suppliedOutput.symm
      have frame := SourceScheduledFrames.Frame.plain (evidence := evidence)
        (tables := tables) (families := families) (required := required)
        (by simpa only [suppliedContext, suppliedScope] using sourceContext)
        (by simpa only [suppliedScope] using scopeTyped) inputSame outputSame
        ((SourceScheduledRecomposition.local_append_nil forest).mpr restCheck)
      have templatesAfter := templates.transport (fun _ _ known => known) (fun _ _ known => known)
        (fun _ _ located => SourceTemplates.CapturedIn.push (frame := .plain supplied) located)
      constructor
      · simpa only [suppliedScope] using RawStep.focus supplied (by simpa only [suppliedContext] using position) stack
      · refine SourceScheduledState.State.checked childSource scopeTyped (.push frame pending (List.Subset.refl _)) (.push closing)
          templatesAfter (.plain matched) childCheck unique ?_ accepted ?_
        · apply RecursiveRequirements.evaluate_sound
          have oldEvaluation := RecursiveRequirements.checked_complete checked
          simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, evaluation] at oldEvaluation
          simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
            RecursiveContexts.plain_context, RecursiveContexts.plain_owners, List.cons_append,
            RecursiveContexts.evaluate_plain]
          simpa only [sameDemand, PhaseRechecking.spendAll_append, ProtectionResiduals.merge_assoc] using oldEvaluation
        · simpa only [sameDemand, List.append_assoc] using accounting

/-- Every source focus rule preserves the shared state and all saved-plan
certificates. No additional child-source or scheduling premise is supplied. -/
theorem focus_preserves
    (state : SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
      scope whole stack forest output demand row evidence)
    (position : Focus whole child context) :
    ∃ (plain : PlainData) (restDependencies : Dependencies) (restPlan : Plan restDependencies),
      plain.context = context ∧ plain.scope = scope ∧
      RawStep ⟨whole, scope, stack⟩ ⟨child, scope, .push (.plain plain) stack⟩ [] [] ∧
      SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
        scope child (.push (.plain plain) stack) (.plain restPlan forest) output demand row evidence := by
  obtain ⟨plain, restDependencies, restPlan, contextSame, scopeSame, admitted⟩ :=
    focus_annotations state position
  exact ⟨plain, restDependencies, restPlan, contextSame, scopeSame,
    admitted plain contextSame scopeSame rfl rfl⟩

end Ash.OneShot.SourceScheduledFocus

#print axioms Ash.OneShot.SourceScheduledFocus.signature_checks
#print axioms Ash.OneShot.SourceScheduledFocus.focus_checked
#print axioms Ash.OneShot.SourceScheduledFocus.focus_annotations
#print axioms Ash.OneShot.SourceScheduledFocus.focus_preserves
