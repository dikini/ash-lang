import SourceAnnotatedDisposal
import SourceAnnotatedRecipeCapture

/-! The annotated source shares one runtime owner registry, action map, name
history and completion invariant. Erasure constructs the existing scheduled
run from those same witnesses. Runtime events still use the scoped machine. -/
namespace Ash.OneShot.SourceAnnotatedRuntime

structure RunState where
  configuration : Configuration
  issued : List Owner
  completed : List Owner

structure NamedState where
  execution : RunState
  activations : List Nat

def NamedState.erase (state : NamedState) : ScopedExecution.NamedState :=
  ⟨⟨state.execution.configuration.erase, state.execution.issued, state.execution.completed⟩, state.activations⟩

def advanceState (before : NamedState) (after : Configuration) (created discharged : List Owner) : NamedState :=
  ⟨⟨after, before.execution.issued ++ created, discharged ++ before.execution.completed⟩,
    before.activations ++ ScopedExecution.enteredActivations before.execution.configuration.erase after.erase⟩

theorem advanceState_erase (before : NamedState) (after : Configuration) (created discharged : List Owner) :
    (advanceState before after created discharged).erase =
      ScopedPortJoint.advanceState before.erase after.erase created discharged := rfl

end Ash.OneShot.SourceAnnotatedRuntime

namespace Ash.OneShot.SourceAnnotatedExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Contracts Value)
open SourceAnnotatedSources (Expression)
open SourcePlanSignatures (signature)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledSavedPlans (Annotations Saved)

section

variable [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy]

/-- The shared execution invariant with its current checking plan exposed.
All original owner, name, access and completion premises are retained. -/
structure AtPlan [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy] (operations : Operations) (declarations : Instantiation.DeclarationRegistry)
    (policy : Syntax.TicketPolicy) (contracts : Contracts) (registry : CoherentSourceTypes.Owners.Registry)
    (tables : CallableProtectionFrames.Tables) (families : SourceDependencyFrames.Families)
    (required : SourceContextualRechecking.Required) (annotations : Annotations) (state : SourceAnnotatedRuntime.NamedState)
    {dependencies : SourceDependencyAnnotations.Dependencies} (plan : SourceDeclarationPlans.Plan dependencies)
    {receiving : SourceDependencyCapture.Scope} {hints : Hints receiving} (forest : Forest hints)
    (output : Value) (demand : List Nat) (row : Footprint) (resultBound : CallableContracts.Contract)
    (evidence : SourcePlannedFrames.DeclarationEvidence := SourcePlannedFrames.recipeEvidence) : Prop where
  coherent : contracts.erase.erase = registry.contracts
  current : DeclaredExecution.Valid operations.erase.erase declarations policy registry tables [] [] state.erase output.erase.erase demand row resultBound
  annotationHistory : ∀ owner captured, annotations owner = some captured → Owner.ticket owner ∈ state.execution.issued
  actions : ∃ tickets,
    ConfigurationUsage policy tickets state.execution.configuration.erase ∧
    UsageRegistryHistory tickets state.execution.issued ∧
    SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required tickets annotations
      (ScopedTyping.resourceWorld state.execution.issued) [] [] state.execution.configuration.scope
      state.execution.configuration.expression state.execution.configuration.stack plan forest output demand row evidence ∧
    DeclaredClosingInvariant.Retained operations.erase.erase.ports (ScopedTyping.resourceWorld state.execution.issued)
      registry tickets state.execution.configuration.stack.erase

structure Run [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy] (operations : Operations) (declarations : Instantiation.DeclarationRegistry)
    (policy : Syntax.TicketPolicy) (contracts : Contracts) (registry : CoherentSourceTypes.Owners.Registry)
    (tables : CallableProtectionFrames.Tables) (families : SourceDependencyFrames.Families)
    (required : SourceContextualRechecking.Required) (annotations : Annotations) (state : SourceAnnotatedRuntime.NamedState)
    {receiving : SourceDependencyCapture.Scope} {hints : Hints receiving} (forest : Forest hints)
    (output : Value) (demand : List Nat) (row : Footprint) (resultBound : CallableContracts.Contract)
    (evidence : SourcePlannedFrames.DeclarationEvidence := SourcePlannedFrames.recipeEvidence) : Prop where
  coherent : contracts.erase.erase = registry.contracts
  current : DeclaredExecution.Valid operations.erase.erase declarations policy registry tables [] [] state.erase output.erase.erase demand row resultBound
  annotationHistory : ∀ owner captured, annotations owner = some captured → Owner.ticket owner ∈ state.execution.issued
  actions : ∃ tickets,
    ConfigurationUsage policy tickets state.execution.configuration.erase ∧
    UsageRegistryHistory tickets state.execution.issued ∧
    SourceAnnotatedRuntimeState.State operations policy contracts tables families required tickets annotations
      (ScopedTyping.resourceWorld state.execution.issued) [] [] state.execution.configuration.scope
      state.execution.configuration.expression state.execution.configuration.stack forest output demand row evidence ∧
    DeclaredClosingInvariant.Retained operations.erase.erase.ports (ScopedTyping.resourceWorld state.execution.issued)
      registry tickets state.execution.configuration.stack.erase


/-- Forget the explicit plan while retaining the same action map and source. -/
theorem AtPlan.run
    (run : AtPlan operations declarations policy contracts registry tables families required annotations state plan forest output demand row resultBound evidence) :
    Run operations declarations policy contracts registry tables families required annotations state forest output demand row resultBound evidence := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  exact ⟨run.coherent, run.current, run.annotationHistory, actions, usage, history, source.state, retained⟩

/-- Expose the source plan already carried by the shared execution witness,
with the same action map, retained data and completion invariant. -/
theorem Run.atPlan
    (run : Run operations declarations policy contracts registry tables families required annotations state forest output demand row resultBound evidence) :
    ∃ dependencies, ∃ plan : SourceDeclarationPlans.Plan dependencies,
      AtPlan operations declarations policy contracts registry tables families required annotations state plan forest output demand row resultBound evidence := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  obtain ⟨_, plan, indexed⟩ := source.atPlan
  exact ⟨_, plan, run.coherent, run.current, run.annotationHistory, actions, usage, history, indexed, retained⟩

/-- The older scheduled source is obtained from the annotated derivation at
the same rich types, action map and stored callback certificates. -/
theorem Run.erase
    (run : Run operations declarations policy contracts registry tables families required annotations state forest output demand row resultBound evidence) :
    SourceScheduledExecution.Run operations declarations policy contracts registry tables families required annotations state.erase forest output demand row resultBound evidence := by
  obtain ⟨actions, usage, history, source, retained⟩ := run.actions
  exact ⟨run.coherent, run.current, run.annotationHistory, actions, usage, history, source.erase, retained⟩

/-- Reuse runtime assembly with the actual annotated successor source. This
is a proof helper; no execution rule assumes successor validity. -/
theorem assemble_entry_atPlan [SourceScheduledChecks.DeclarationProjection admission certification]
    (coherent : contracts.erase.erase = registry.contracts)
    (current : DeclaredExecution.Valid operations.erase.erase declarations policy registry tables [] [] before.erase output.erase.erase demand row resultBound)
    (raw : RawStep before.execution.configuration.erase after.erase created discharged)
    (freshOwners : (before.execution.issued ++ created).Nodup)
    (freshHandlers : (before.activations ++ enteredActivations before.execution.configuration.erase after.erase).Nodup)
    (checks : AccessChecks before.execution.configuration.erase [])
    (usage : ConfigurationUsage policy actions before.execution.configuration.erase)
    (history : UsageRegistryHistory actions before.execution.issued)
    (annotationHistory : ∀ owner captured, annotations owner = some captured → Owner.ticket owner ∈ before.execution.issued)
    (retained : DeclaredClosingInvariant.Retained operations.erase.erase.ports (ScopedTyping.resourceWorld before.execution.issued)
      registry actions before.execution.configuration.stack.erase)
    (source : SourceAnnotatedRuntimeState.AtPlan operations policy contracts nextTables nextFamilies nextRequired
      (ScopedActionUsage.advance actions after.erase created) annotations (ScopedTyping.resourceWorld (before.execution.issued ++ created)) [] []
      after.scope after.expression after.stack plan forest output nextDemand nextRow evidence)
    (results : CompletionFrames.ConfigurationReturns declarations registry.runtime.results
      (ScopedTyping.resourceWorld (before.execution.issued ++ created)) after.erase resultBound)
    (update : registry.runtime.joint.usage = advanceUsageTickets policy registry.runtime.joint.usage after.erase created)
    (noTickets : ∀ owner, Owner.ticket owner ∉ created) :
    AtPlan operations declarations policy contracts registry nextTables nextFamilies nextRequired annotations
      (SourceAnnotatedRuntime.advanceState before after created discharged) plan forest output nextDemand nextRow resultBound evidence := by
  have existing := SourceScheduledExecution.assemble_entry coherent current raw freshOwners freshHandlers checks usage history
    annotationHistory retained source.state.erase results update noTickets
  have usageChecks := usage_checks_from_allocation_and_access history freshOwners checks
  have extension := ScopedActionUsage.advance_extends (after := after.erase) usageChecks.allocation
  have unique : (ownedTickets after.stack.erase).Nodup := by
    cases source with
    | checked _ _ _ _ _ _ _ unique _ _ _ => exact unique
  have larger : ScopedTyping.resourceWorld before.execution.issued ⊆
      ScopedTyping.resourceWorld (before.execution.issued ++ created) := by
    rw [ScopedTyping.resource_world_append]
    exact List.subset_append_left _ _
  exact ⟨coherent, existing.current, existing.annotationHistory,
    _, ScopedActionUsage.raw_step_preserves raw usageChecks usage,
    ScopedActionUsage.raw_step_preserves_history raw history, source,
    DeclaredClosingInvariant.raw_step_preserves_retained raw retained (fun _ _ known => known)
      extension larger (.none noTickets) unique⟩

theorem assemble_entry [SourceScheduledChecks.DeclarationProjection admission certification]
    (coherent : contracts.erase.erase = registry.contracts)
    (current : DeclaredExecution.Valid operations.erase.erase declarations policy registry tables [] [] before.erase output.erase.erase demand row resultBound)
    (raw : RawStep before.execution.configuration.erase after.erase created discharged)
    (freshOwners : (before.execution.issued ++ created).Nodup)
    (freshHandlers : (before.activations ++ enteredActivations before.execution.configuration.erase after.erase).Nodup)
    (checks : AccessChecks before.execution.configuration.erase [])
    (usage : ConfigurationUsage policy actions before.execution.configuration.erase)
    (history : UsageRegistryHistory actions before.execution.issued)
    (annotationHistory : ∀ owner captured, annotations owner = some captured → Owner.ticket owner ∈ before.execution.issued)
    (retained : DeclaredClosingInvariant.Retained operations.erase.erase.ports (ScopedTyping.resourceWorld before.execution.issued)
      registry actions before.execution.configuration.stack.erase)
    (source : SourceAnnotatedRuntimeState.State operations policy contracts nextTables nextFamilies nextRequired
      (ScopedActionUsage.advance actions after.erase created) annotations (ScopedTyping.resourceWorld (before.execution.issued ++ created)) [] []
      after.scope after.expression after.stack forest output nextDemand nextRow evidence)
    (results : CompletionFrames.ConfigurationReturns declarations registry.runtime.results
      (ScopedTyping.resourceWorld (before.execution.issued ++ created)) after.erase resultBound)
    (update : registry.runtime.joint.usage = advanceUsageTickets policy registry.runtime.joint.usage after.erase created)
    (noTickets : ∀ owner, Owner.ticket owner ∉ created) :
    Run operations declarations policy contracts registry nextTables nextFamilies nextRequired annotations
      (SourceAnnotatedRuntime.advanceState before after created discharged) forest output nextDemand nextRow resultBound evidence := by
  cases source with
  | checked currentSource scope pending closing templates matched contextual unique evaluated accepted accounting =>
      exact (assemble_entry_atPlan coherent current raw freshOwners freshHandlers checks usage history annotationHistory retained
        (.checked currentSource scope pending closing templates matched contextual unique evaluated accepted accounting)
        results update noTickets).run

/-- Initial runtime assembly still exposes source, scheduling, completion and
signature admission separately. It is not a complete source-admission theorem. -/
theorem initial_atPlan {plan : SourceDeclarationPlans.Plan dependencies}
    (source : Expression operations policy (fun _ => none) [] [] .none (fun _ => none)
      code output demand requirements (signature plan))
    (contextual : SourceScheduledChecks.Local [] (fun _ => none) (OwnerPhaseTransitions.available []) [] plan .nil)
    (admitted : SourceScheduledExecution.checkInitial code.erase requirements = true)
    (result : CompletionContracts.Derives declarations CallableContracts.Environment.empty [] .none code.erase resultBound)
    (signature : operations.erase.erase.ports = DeclarationResults.signature declarations) :
    demand = [] ∧ AtPlan operations declarations policy (fun _ => none) (fun _ => none) tables families required (fun _ => none)
      ⟨⟨⟨code, .none, .nil⟩, [], []⟩, []⟩ plan .nil output [] [] resultBound evidence := by
  obtain ⟨evaluated, supported⟩ := SourceScheduledExecution.checkInitial_iff.mp admitted
  have accepted : checkFootprint [] [] = true := rfl
  have support : decide (Syntax.resourceDependencies code.erase.dependencies = []) = true := by simpa using supported
  obtain ⟨empty, existing⟩ := DeclaredConnectedSources.initial_run
    (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase source.erase))
    evaluated accepted result signature support (tables := tables)
  obtain ⟨actions, usage, history, oldSource, retained⟩ := existing.actions
  have permissions : Syntax.UsageExtension (fun _ => none) actions := by intro owner rights known; cases known
  have checked := SourceScheduledTransport.local_transport contextual (fun _ ready => ready) permissions
  exact ⟨empty, rfl, existing.current, (by intro owner captured known; cases known), actions, usage, history,
    empty ▸ SourceAnnotatedRuntimeState.AtPlan.initial source empty checked evaluated accepted, retained⟩

theorem initial_run {plan : SourceDeclarationPlans.Plan dependencies}
    (source : Expression operations policy (fun _ => none) [] [] .none (fun _ => none)
      code output demand requirements (signature plan))
    (contextual : SourceScheduledChecks.Local [] (fun _ => none) (OwnerPhaseTransitions.available []) [] plan .nil)
    (admitted : SourceScheduledExecution.checkInitial code.erase requirements = true)
    (result : CompletionContracts.Derives declarations CallableContracts.Environment.empty [] .none code.erase resultBound)
    (signature : operations.erase.erase.ports = DeclarationResults.signature declarations) :
    demand = [] ∧ Run operations declarations policy (fun _ => none) (fun _ => none) tables families required (fun _ => none)
      ⟨⟨⟨code, .none, .nil⟩, [], []⟩, []⟩ .nil output [] [] resultBound evidence := by
  obtain ⟨empty, run⟩ := initial_atPlan source contextual admitted result signature
  exact ⟨empty, run.run⟩

end


end Ash.OneShot.SourceAnnotatedExecution

#print axioms Ash.OneShot.SourceAnnotatedRuntime.advanceState_erase
#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.erase
#print axioms Ash.OneShot.SourceAnnotatedExecution.assemble_entry
#print axioms Ash.OneShot.SourceAnnotatedExecution.initial_run

#print axioms Ash.OneShot.SourceAnnotatedExecution.AtPlan.run
#print axioms Ash.OneShot.SourceAnnotatedExecution.assemble_entry_atPlan
#print axioms Ash.OneShot.SourceAnnotatedExecution.initial_atPlan

#print axioms Ash.OneShot.SourceAnnotatedExecution.Run.atPlan
