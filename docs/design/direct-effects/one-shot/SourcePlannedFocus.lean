import SourcePlannedContexts
import SourcePlannedNeutralChecks

/-! The same source focus decomposition now retains its local checking plans.
Pure-frame transport handles the right-pair context; all other cases reuse
sequencing inversion. Actual frame preparation and ownership traces are reused. -/
namespace Ash.OneShot.SourcePlannedSources
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements evaluate)
open ProtectionResiduals (merge)
open OwnerPhaseTransitions (spendAll)
open SourceDependencyAnnotations (Dependencies)
open SourcePlannedTyping (Value)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (Signature signature)
open SourceContextualHints (Hints)
open SourcePlannedChecks (Local Pending)

/-- The signature split selects actual plan witnesses from the original
check, retaining all clause annotations. It assumes no new child check. -/
theorem FocusSignature.local_checks {whole : Signature wholeDependencies}
    {child : Signature childDependencies} {rest : Signature restDependencies}
    (split : FocusSignature whole child rest) {plan : Plan wholeDependencies}
    (same : signature plan = whole) (checked : Local outward actions phases world plan hints) :
    ∃ childPlan : Plan childDependencies, ∃ restPlan : Plan restDependencies,
      signature childPlan = child ∧ signature restPlan = rest ∧
      Local outward actions phases world childPlan (.plain (dependencies := restDependencies) hints) ∧
      Local outward actions phases world restPlan hints := by
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
              SourcePlannedNeutralChecks.local_transport secondCheck (.extra .refl), .pure⟩
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
theorem focus_checked {plan : Plan dependencies} {hints : Hints receiving}
    (source : Expression operations policy contracts world allowed scope environment whole output demand requirements (signature plan))
    (checked : Local outward actions phases world plan hints)
    (focus : Focus whole child position) :
    ∃ (input : Value) (childDemand restDemand : List Nat) (current : Requirements childDemand) (rest : Requirements restDemand)
      (childDependencies restDependencies : Dependencies) (childPlan : Plan childDependencies) (restPlan : Plan restDependencies),
      Expression operations policy contracts world allowed scope environment child input childDemand current (signature childPlan) ∧
      Context operations policy contracts world environment allowed scope position input output restDemand rest (signature restPlan) ∧
      Local outward actions phases world childPlan (.plain (dependencies := restDependencies) hints) ∧
      Local outward actions phases world restPlan hints ∧
      demand = childDemand ++ restDemand ∧
      ∀ store receiving before, evaluate store receiving before requirements =
        merge (evaluate store receiving before current) (evaluate store receiving (spendAll before childDemand) rest) := by
  obtain ⟨input, childDemand, restDemand, current, rest, childDependencies, restDependencies, childSignature, restSignature,
    childSource, context, split, sameDemand, evaluation⟩ := focus_decompose source focus
  obtain ⟨childPlan, restPlan, childSame, restSame, childCheck, restCheck⟩ := split.local_checks rfl checked
  exact ⟨input, childDemand, restDemand, current, rest, childDependencies, restDependencies, childPlan, restPlan,
    by simpa only [childSame] using childSource,
    by simpa only [restSame] using context,
    childCheck, restCheck, sameDemand, evaluation⟩

/-- Construct the actual focus step from these same source and checking
witnesses. The existing preparation theorem fixes the frame's metadata. -/
theorem focus_checked_step {plan : Plan dependencies} {hints : Hints receiving}
    (source : Expression operations policy contracts world allowed scope (fun _ => none) whole output demand requirements (signature plan))
    (checked : Local outward actions phases world plan hints)
    (pending : Pending outward actions phases world hints .nil)
    (matched : SourceContextualHintChecking.Matches tables families required hints stack)
    (focus : Focus whole child position)
    (scopeTyped : ScopedPorts.EffectScope contracts.erase.erase.ports scope ticket) :
    ∃ (input : Value) (childDemand restDemand : List Nat) (current : Requirements childDemand) (rest : Requirements restDemand)
      (childDependencies restDependencies : Dependencies) (childPlan : Plan childDependencies) (restPlan : Plan restDependencies)
      (plain : PlainData),
      RawStep ⟨whole, scope, stack⟩ ⟨child, scope, .push (.plain plain) stack⟩ [] [] ∧
      Expression operations policy contracts world allowed scope (fun _ => none) child input childDemand current (signature childPlan) ∧
      Context operations policy contracts world (fun _ => none) allowed plain.scope plain.context input output restDemand rest (signature restPlan) ∧
      SourceDependencyFrames.Frame operations.erase policy contracts.erase tables families world (.plain plain)
        input.erase output.erase restDemand rest (.plain restDependencies) allowed allowed ∧
      SourceContextualHintChecking.Matches tables families required (.plain (dependencies := restDependencies) hints)
        (.push (.plain plain) stack) ∧
      Local outward actions phases world childPlan (.plain (dependencies := restDependencies) hints) ∧
      Pending outward actions phases world (.plain (dependencies := restDependencies) hints) .nil ∧
      demand = childDemand ++ restDemand ∧
      (∀ store receiving before, evaluate store receiving before requirements =
        merge (evaluate store receiving before current) (evaluate store receiving (spendAll before childDemand) rest)) ∧
      OwnerPhaseTransitions.Trace (OwnerPhaseTransitions.available (ownedTickets stack)) []
        (OwnerPhaseTransitions.available (ownedTickets (.push (.plain plain) stack))) := by
  obtain ⟨input, childDemand, restDemand, current, rest, childDependencies, restDependencies, childPlan, restPlan,
    childSource, context, childCheck, restCheck, same, evaluation⟩ := focus_checked source checked focus
  obtain ⟨plain, contextSame, scopeSame, inputAnnotation, outputAnnotation⟩ := RecursiveContexts.prepare_plain
    (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase (expression_erase source)))
    focus scopeTyped input.erase.erase
  have synchronized : Context operations policy contracts world (fun _ => none) allowed plain.scope plain.context
      input output restDemand rest (signature restPlan) := by simpa only [contextSame, scopeSame] using context
  have framePending : Pending outward actions phases world (.plain (dependencies := restDependencies) hints) .nil := by
    exact .plain ((SourcePlannedRecomposition.local_append_nil hints).mpr restCheck) pending
  refine ⟨input, childDemand, restDemand, current, rest, childDependencies, restDependencies, childPlan, restPlan,
    plain, ?_, childSource, synchronized,
    synchronized.plain_frame (by simpa only [scopeSame] using scopeTyped) inputAnnotation outputAnnotation,
    .plain matched, childCheck, framePending, same, evaluation, .nil⟩
  simpa only [scopeSame] using RawStep.focus plain (by simpa only [contextSame] using focus) stack

end Ash.OneShot.SourcePlannedSources

#print axioms Ash.OneShot.SourcePlannedSources.FocusSignature.local_checks
#print axioms Ash.OneShot.SourcePlannedSources.focus_checked
#print axioms Ash.OneShot.SourcePlannedSources.focus_checked_step
