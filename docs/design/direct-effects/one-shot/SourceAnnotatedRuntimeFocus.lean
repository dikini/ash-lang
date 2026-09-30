import SourceAnnotatedRuntimeState
import SourceAnnotatedBoundFocus
import SourceBoundSnapshots

/-! Every annotated focus form preserves the shared scheduled state. Its frame
ports are checked against the actual child hint and retained stack; no source
or successor-state proof is stored in the transition guard. -/
namespace Ash.OneShot.SourceAnnotatedRuntimeFocus
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

theorem focus_checked {plan : Plan dependencies} {hints : Hints receiving} {forest : Forest hints}
    (source : Expression operations policy contracts world allowed scope environment whole output demand requirements (signature plan))
    (checked : Local outward actions phases world plan forest)
    (focus : SourceAnnotatedCode.Focus whole child position) :
    ∃ (input : Value) (childDemand restDemand : List Nat) (current : Requirements childDemand) (rest : Requirements restDemand)
      (childDependencies restDependencies : Dependencies) (childPlan : Plan childDependencies) (restPlan : Plan restDependencies),
      Expression operations policy contracts world allowed scope environment child input childDemand current (signature childPlan) ∧
      Context operations policy contracts world environment allowed scope position input output restDemand rest (signature restPlan) ∧
      Local outward actions phases world childPlan (.plain restPlan forest) ∧
      Local outward actions phases world restPlan forest ∧
      demand = childDemand ++ restDemand ∧
      ∀ store receiving before, evaluate store receiving before requirements =
        merge (evaluate store receiving before current) (evaluate store receiving (spendAll before childDemand) rest) := by
  obtain ⟨input, childDemand, restDemand, current, rest, childDependencies, restDependencies, childPlan, restPlan,
    childBounds, restBounds, childSource, context, childCheck, restCheck, retained, sameDemand, evaluation⟩ :=
    focus_checked_bounds source checked .absent focus
  exact ⟨input, childDemand, restDemand, current, rest, childDependencies, restDependencies, childPlan, restPlan,
    childSource, context, childCheck, restCheck, sameDemand, evaluation⟩


/-- The shared focus proof retains source metadata with the actual child and
queued plan. The ordinary API below is its metadata-absent specialization. -/
theorem focus_parts_preserves_bounds {plain : SourceAnnotatedRuntime.Plain} {plan : Plan dependencies}
    (current : Expression operations policy contracts world allowed plain.scope (fun _ => none)
      whole input currentDemand currentRequirements (signature plan))
    (scopeTyped : ScopedPorts.EffectScope contracts.erase.erase.ports plain.scope ticket)
    (pending : SourceAnnotatedRuntimeTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward
      (OwnerPhaseTransitions.available (ownedTickets stack.erase)) world
      stack input output pendingDemand pendingRequirements resumes forest .nil allowed [])
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
      SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
        plain.scope child (.push (.plain plain) stack) childPlan (.plain restPlan forest) output demand row evidence ∧
      SourcePlanBounds.Focused world bounds childBounds restBounds := by
  obtain ⟨input, childDemand, restDemand, currentReq, restReq, childDependencies, restDependencies, childPlan, restPlan,
    childBounds, restBounds, childSource, sourceContext, childCheck, restCheck, retainedBounds, sameDemand, evaluation⟩ :=
      focus_checked_bounds current contextual bounds position
  have ports := SourceFocusHints.source_frame_agreement childSource.hint_checked guard
  have frame := SourceAnnotatedRuntimeTyping.Frame.plain (evidence := evidence)
    (tables := tables) (families := families) (required := required)
    sourceContext (by simpa only [position.output_hint] using current.hint_checked)
    (position.context_closed current.resource_closed) scopeTyped ports.1.symm
    (ports.2.trans pending.input_port).symm
    ((SourceScheduledRecomposition.local_append_nil forest).mpr restCheck)
  have templatesAfter := templates.transport (fun _ _ known => known) (fun _ _ known => known)
    (fun _ _ located => SourceAnnotatedRuntime.CapturedIn.push (frame := .plain plain) located)
  refine ⟨childDependencies, restDependencies, childPlan, restPlan, childBounds, restBounds,
    SourceAnnotatedRuntime.focus_executes plain position stack,
    SourceAnnotatedRuntimeState.AtPlan.checked childSource scopeTyped (.push frame pending (List.Subset.refl _)) (.push closing)
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

/-- All ten contexts use one finite port guard. The successor's annotated
current source, saved context and scheduling derivation are conclusions. -/
theorem focus_preserves {plain : SourceAnnotatedRuntime.Plain}
    (state : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      plain.scope whole stack forest output demand row evidence)
    (position : SourceAnnotatedCode.Focus whole child plain.context)
    (guard : SourceAnnotatedCode.checkFocusFrame Instantiation.Environment.empty child output.erase.erase.port stack.erase plain.erase = true) :
    ∃ (restDependencies : Dependencies) (restPlan : Plan restDependencies),
      RawStep
        (SourceAnnotatedRuntime.Configuration.erase ⟨whole, plain.scope, stack⟩)
        (SourceAnnotatedRuntime.Configuration.erase ⟨child, plain.scope, .push (.plain plain) stack⟩) [] [] ∧
      SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
        plain.scope child (.push (.plain plain) stack) (.plain restPlan forest) output demand row evidence := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique checked accepted accounting =>
      obtain ⟨childDependencies, restDependencies, childPlan, restPlan, childBounds, restBounds, step, next, retained⟩ :=
        focus_parts_preserves_bounds current scopeTyped pending closing templates matched contextual unique checked accepted accounting
          .absent position guard
      exact ⟨restDependencies, restPlan, step, next.state⟩

/-- The current source constructs a frame that passes the guard, so retaining
annotations introduces no additional failure at an existing focus position. -/
theorem focus_progress
    (state : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      scope whole stack forest output demand row evidence)
    (position : SourceAnnotatedCode.Focus whole child context) :
    ∃ (plain : SourceAnnotatedRuntime.Plain) (restDependencies : Dependencies) (restPlan : Plan restDependencies),
      plain.context = context ∧ plain.scope = scope ∧
      SourceAnnotatedCode.checkFocusFrame Instantiation.Environment.empty child output.erase.erase.port stack.erase plain.erase = true ∧
      RawStep (SourceAnnotatedRuntime.Configuration.erase ⟨whole, scope, stack⟩)
        (SourceAnnotatedRuntime.Configuration.erase ⟨child, scope, .push (.plain plain) stack⟩) [] [] ∧
      SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
        scope child (.push (.plain plain) stack) (.plain restPlan forest) output demand row evidence := by
  have original := state
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique checked accepted accounting =>
      obtain ⟨input, childDemand, restDemand, currentReq, restReq, childDependencies, restDependencies,
        childSignature, restSignature, raw, childSource, contextSource, contextSame, scopeSame, frame, rawStep,
        guard, hint, split, same, evaluation⟩ := SourceAnnotatedSources.focus_prepare (tables := tables) (families := families)
          current position scopeTyped pending.input_port.symm
      let plain := SourceAnnotatedRuntime.Plain.ofRaw raw context contextSame.symm
      have sameScope : plain.scope = scope := scopeSame
      have guarded : SourceAnnotatedCode.checkFocusFrame Instantiation.Environment.empty child output.erase.erase.port stack.erase plain.erase = true := by
        simpa only [plain, SourceAnnotatedRuntime.Plain.erase_ofRaw] using guard
      obtain ⟨restDependencies, restPlan, step, next⟩ := focus_preserves
        (plain := plain) (by simpa only [sameScope] using original) position guarded
      exact ⟨plain, restDependencies, restPlan, rfl, sameScope, guarded,
        by simpa only [sameScope] using step, by simpa only [sameScope] using next⟩

/-- Focus now advances persistent metadata and the plan-indexed refinement of
the shared state together. Exact queue retention is a data equation. -/
theorem focus_snapshot {plain : SourceAnnotatedRuntime.Plain}
    (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
      plain.scope whole stack snapshot.plan snapshot.forest output demand row evidence)
    (position : SourceAnnotatedCode.Focus whole child plain.context)
    (guard : SourceAnnotatedCode.checkFocusFrame Instantiation.Environment.empty child output.erase.erase.port stack.erase plain.erase = true) :
    ∃ (childDependencies restDependencies : Dependencies) (childPlan : Plan childDependencies) (restPlan : Plan restDependencies),
      ∃ childBounds : SourcePlanBounds.Annotation world childPlan, ∃ restBounds : SourcePlanBounds.Annotation world restPlan,
      let next := snapshot.focus childPlan restPlan childBounds restBounds
      RawStep
        (SourceAnnotatedRuntime.Configuration.erase ⟨whole, plain.scope, stack⟩)
        (SourceAnnotatedRuntime.Configuration.erase ⟨child, plain.scope, .push (.plain plain) stack⟩) [] [] ∧
      SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
        plain.scope child (.push (.plain plain) stack) next.plan next.forest output demand row evidence ∧
      SourcePlanBounds.Focused world snapshot.current childBounds restBounds := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique checked accepted accounting =>
      exact focus_parts_preserves_bounds current scopeTyped pending closing templates matched contextual unique checked accepted accounting
        snapshot.current position guard

omit [SourceScheduledChecks.DeclarationProjection admission certification] in
/-- Existing initial-state premises also establish the explicit source
snapshot. This does not derive the separate initial admission premises. -/
theorem initial_snapshot {plan : Plan dependencies}
    (current : Expression operations policy contracts world [] .none (fun _ => none)
      code output demand requirements (signature plan))
    (bounds : SourcePlanBounds.Annotation world plan)
    (empty : demand = [])
    (contextual : Local outward actions (OwnerPhaseTransitions.available []) world plan .nil)
    (evaluated : RecursiveRequirements.Checked [] [] (OwnerPhaseTransitions.available []) requirements row)
    (accepted : checkFootprint outside row = true) :
    let snapshot : SourceBoundSnapshots.Snapshot world := ⟨_, plan, bounds, _, .nil, .nil, .nil⟩
    SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
      .none code .nil snapshot.plan snapshot.forest output demand row evidence :=
  SourceAnnotatedRuntimeState.AtPlan.initial current empty contextual evaluated accepted

end Ash.OneShot.SourceAnnotatedRuntimeFocus

#print axioms Ash.OneShot.SourceAnnotatedRuntimeFocus.focus_checked
#print axioms Ash.OneShot.SourceAnnotatedRuntimeFocus.focus_preserves

#print axioms Ash.OneShot.SourceAnnotatedRuntimeFocus.focus_progress

#print axioms Ash.OneShot.SourceAnnotatedRuntimeFocus.focus_parts_preserves_bounds
#print axioms Ash.OneShot.SourceAnnotatedRuntimeFocus.focus_snapshot
#print axioms Ash.OneShot.SourceAnnotatedRuntimeFocus.initial_snapshot
