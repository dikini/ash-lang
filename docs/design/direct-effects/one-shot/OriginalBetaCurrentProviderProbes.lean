import CoreCallableOriginalBetaCurrent
namespace Ash.OneShot.OriginalBetaCurrentProviderProbes
open CoreCallableOriginalHigherCurrent.Original CoreCallableOriginalBetaCurrent.Original
open CoreCallableOriginalCallableCurrent.Original
open CoreCallableComposedRuntimeCalls.Original
local instance : SourcePlannedChecks.DeclarationPolicy := SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

/-- One SAME original graph starts with the executed installed Program receipt
and reaches the exact first private rich beta endpoint in 21 actual Core edges. -/
theorem original_initial_to_first_beta : Nonempty InstalledFirstBeta := installed_first_beta

theorem original_full_domain : higherInput = readerContract := rfl

theorem scalar_domain_erasure_rejected (produced : InstalledFirstBeta) :
    produced.higher.path.stored.value 0 ≠
      CallableContracts.Contract.function [] (.storage []) (.storage []) :=
  CoreCallableRichBetaCore.OriginalAuthority.retained_domain_not_scalar produced.higher.path

theorem exact_chosen_family (produced : InstalledFirstBeta) :
    produced.beta.selected.family = produced.higher.origin.family := produced.beta.chosen

theorem exact_private_successor (produced : InstalledFirstBeta) :
    produced.beta.next.sourceDemand = produced.beta.selected.family.demand ∧
    HEq produced.beta.next.requirements produced.beta.selected.family.requirements ∧
    HEq produced.beta.next.plan produced.beta.selected.nextPlan ∧
    HEq produced.beta.next.rows produced.beta.selected.nextRows :=
  ⟨produced.beta.exactDemand,produced.beta.exactRequirements,produced.beta.exactPlan,produced.beta.exactRows⟩

theorem actual_reader_support (produced : InstalledFirstBeta) :
    (originalCall produced.higher).argument = [0,0] := argument_support produced.higher

theorem same_runtime_callee (produced : InstalledFirstBeta) :
    e21.state.control = .evaluate 9 higherBodyEnvironment ∧ e21.history = e20.history :=
  ⟨produced.beta.callee,produced.beta.history⟩

theorem current_first_beta (produced : InstalledFirstBeta) :
    CoreCallableRichBetaCore.Current e21 produced.beta.next := produced.beta.related

theorem actual_bind_focus :
    CoreMachine.next G e15.state = .stepped e16.state ∧
      CoreCallableGeneratedChronology.Matching G e15 e16 [] [] :=
  CoreCallableGeneratedChronology.Operation.actual (.bind bindInput)

theorem ranked_operand_administration :
    CoreCallableGeneratedChronology.Matching G e16 e17 [] [] ∧
    CoreCallableGeneratedChronology.Matching G e17 e18 [] [] ∧
    CoreCallableGeneratedChronology.Matching G e18 e19 [] [] ∧
    CoreCallableGeneratedChronology.Matching G e19 e20 [] [] :=
  ⟨(CoreCallableGeneratedChronology.Operation.actual (.entry outerEntry)).2,
   (CoreCallableGeneratedChronology.Operation.actual (.literal outerFunction)).2,
   (CoreCallableGeneratedChronology.Operation.actual (.swap outerSwap)).2,
   (CoreCallableGeneratedChronology.Operation.actual (.literal outerArgument)).2⟩

#print axioms actual_bind_focus
#print axioms ranked_operand_administration
#print axioms original_initial_to_first_beta
#print axioms original_full_domain
#print axioms scalar_domain_erasure_rejected
#print axioms exact_chosen_family
#print axioms exact_private_successor
#print axioms actual_reader_support
#print axioms same_runtime_callee
#print axioms current_first_beta
end Ash.OneShot.OriginalBetaCurrentProviderProbes
