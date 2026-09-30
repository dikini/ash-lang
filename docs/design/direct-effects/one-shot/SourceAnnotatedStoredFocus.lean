import SourceAnnotatedStoredState
import SourceAnnotatedBoundFocus
import SourceBoundSnapshots

/-! Every annotated focus form preserves the shared scheduled state. Its frame
ports are checked against the actual child hint and retained stack; no source
or successor-state proof is stored in the transition guard. -/
namespace Ash.OneShot.SourceAnnotatedStoredFocus
open SourceAnnotatedRuntimeFocus (focus_checked_bounds)
open ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements evaluate)
open ProtectionResiduals (merge)
open OwnerPhaseTransitions (spendAll)
open SourceDependencyAnnotations (Dependencies)
open SourcePlannedTyping (Value)
open SourceAnnotatedSources (Expression Context focus_decompose)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (Signature signature)
open SourceContextualHints (Hints)
open SourceScheduledChecks (Local Pending)
open SourceRetainedPlans (Forest)

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

theorem focus_parts_preserves_bounds {plain : SourceAnnotatedRuntime.Plain} {plan : Plan dependencies}
    (current : Expression operations policy contracts world allowed plain.scope (fun _ => none)
      whole input currentDemand currentRequirements (signature plan))
    (scopeTyped : ScopedPorts.EffectScope contracts.erase.erase.ports plain.scope ticket)
    (pending : SourceAnnotatedStoredTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward
      (OwnerPhaseTransitions.available (ownedTickets stack.erase)) world
      stack input output pendingDemand pendingRequirements resumes forest .nil allowed [] stored)
    (closing : DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world stack.erase disposals)
    (templates : SourceAnnotatedClosingRecords.Records operations policy contracts tables annotations world stack disposals)
    (matched : SourceScheduledSavedPlans.Matches annotations forest)
    (contextual : Local outward actions (OwnerPhaseTransitions.available (ownedTickets stack.erase)) world plan forest)
    (unique : (ownedTickets stack.erase).Nodup)
    (checked : RecursiveRequirements.Checked (resumes ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack.erase))
      (.sequence (currentRequirements.prepend (OwnerPhases.ofStack tables stack.erase)) pendingRequirements) row)
    (accepted : checkFootprint outside row = true)
    (accounting : demand = currentDemand ++ pendingDemand)
    (bounds : SourcePlanBounds.Annotation world plan)
    (position : SourceAnnotatedCode.Focus whole child plain.context)
    (guard : SourceAnnotatedCode.checkFocusFrame Instantiation.Environment.empty child output.erase.erase.port stack.erase plain.erase = true) :
    ∃ (childDependencies restDependencies : Dependencies) (childPlan : Plan childDependencies) (restPlan : Plan restDependencies),
      ∃ childBounds : SourcePlanBounds.Annotation world childPlan, ∃ restBounds : SourcePlanBounds.Annotation world restPlan,
      RawStep
        (SourceAnnotatedRuntime.Configuration.erase ⟨whole, plain.scope, stack⟩)
        (SourceAnnotatedRuntime.Configuration.erase ⟨child, plain.scope, .push (.plain plain) stack⟩) [] [] ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
        plain.scope child (.push (.plain plain) stack) childPlan (.plain restPlan forest) output demand row (.push .plain stored) evidence ∧
      SourcePlanBounds.Focused world bounds childBounds restBounds := by
  obtain ⟨input, childDemand, restDemand, currentReq, restReq, childDependencies, restDependencies, childPlan, restPlan,
    childBounds, restBounds, childSource, sourceContext, childCheck, restCheck, retainedBounds, sameDemand, evaluation⟩ :=
      focus_checked_bounds current contextual bounds position
  have ports := SourceFocusHints.source_frame_agreement childSource.hint_checked guard
  have frame := SourceAnnotatedRuntimeTyping.Frame.plain (evidence := evidence)
    (tables := tables) (families := families) (required := required)
    sourceContext (by simpa only [position.output_hint] using current.hint_checked)
    (position.context_closed current.resource_closed) scopeTyped ports.1.symm
    (ports.2.trans pending.forget.input_port).symm
    ((SourceScheduledRecomposition.local_append_nil forest).mpr restCheck)
  have templatesAfter := templates.transport (fun _ _ known => known) (fun _ _ known => known)
    (fun _ _ located => SourceAnnotatedRuntime.CapturedIn.push (frame := .plain plain) located)
  refine ⟨childDependencies, restDependencies, childPlan, restPlan, childBounds, restBounds,
    SourceAnnotatedRuntime.focus_executes plain position stack,
    SourceAnnotatedRuntimeState.AtPackets.checked childSource scopeTyped (.push ⟨frame, .plain⟩ pending (List.Subset.refl _)) (.push closing)
      templatesAfter (.plain matched) childCheck unique ?_ accepted ?_, retainedBounds⟩
  · apply RecursiveRequirements.evaluate_sound
    have oldEvaluation := RecursiveRequirements.checked_complete checked
    simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, evaluation] at oldEvaluation
    simp only [SourceAnnotatedRuntime.Stack.erase, SourceAnnotatedRuntime.Frame.erase,
      RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
      RecursiveContexts.plain_context, RecursiveContexts.plain_owners, List.cons_append,
      RecursiveContexts.evaluate_plain]
    simpa only [sameDemand, PhaseRechecking.spendAll_append, ProtectionResiduals.merge_assoc] using oldEvaluation
  · simpa only [sameDemand, List.append_assoc] using accounting

theorem focus_snapshot {plain : SourceAnnotatedRuntime.Plain}
    (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
      plain.scope whole stack snapshot.plan snapshot.forest output demand row stored evidence)
    (position : SourceAnnotatedCode.Focus whole child plain.context)
    (guard : SourceAnnotatedCode.checkFocusFrame Instantiation.Environment.empty child output.erase.erase.port stack.erase plain.erase = true) :
    ∃ (childDependencies restDependencies : Dependencies) (childPlan : Plan childDependencies) (restPlan : Plan restDependencies),
      ∃ childBounds : SourcePlanBounds.Annotation world childPlan, ∃ restBounds : SourcePlanBounds.Annotation world restPlan,
      let next := snapshot.focus childPlan restPlan childBounds restBounds
      RawStep
        (SourceAnnotatedRuntime.Configuration.erase ⟨whole, plain.scope, stack⟩)
        (SourceAnnotatedRuntime.Configuration.erase ⟨child, plain.scope, .push (.plain plain) stack⟩) [] [] ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
        plain.scope child (.push (.plain plain) stack) next.plan next.forest output demand row (.push .plain stored) evidence ∧
      SourcePlanBounds.Focused world snapshot.current childBounds restBounds := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique checked accepted accounting =>
      exact focus_parts_preserves_bounds current scopeTyped pending closing templates matched contextual unique checked accepted accounting
        snapshot.current position guard

end Ash.OneShot.SourceAnnotatedStoredFocus

#print axioms Ash.OneShot.SourceAnnotatedStoredFocus.focus_parts_preserves_bounds
#print axioms Ash.OneShot.SourceAnnotatedStoredFocus.focus_snapshot
