import SourceAnnotatedRuntimeTyping
import SourceAnnotatedClosingRecords
import SourceBoundComputation

/-! Current and recursively saved runtime syntax retain one annotated source
judgment. Stored closing records also retain annotated callback sources.
Erasure constructs the established scheduled state with the same rich types,
plans and checks. Full runtime preservation remains separate. -/
namespace Ash.OneShot.SourceAnnotatedRuntimeState
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Contracts Value)
open SourceAnnotatedSources (Expression)
open SourceAnnotatedCode (Term)
open SourceDependencyCapture (lookupDependencies)
open SourceDependencyAnnotations (Dependencies)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceRetainedPlans (Forest)
open SourceScheduledSavedPlans (Annotations)
open SourcePlannedFrames (DeclarationEvidence recipeEvidence)
open RecursiveRequirements (Requirements)
open SourcePlanBounds (Annotation Reduced)

section

variable [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy]

/-- The existing state premises with the current plan exposed as an index.
Bound snapshots use this to share the exact source witness. -/
inductive AtPlan [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy] (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (families : SourceDependencyFrames.Families)
    (required : SourceContextualRechecking.Required) (actions : Syntax.UsageTickets) (annotations : Annotations)
    (world : List Nat) (outward : List Instance) (outside : ProtectionContracts.Context)
    (scope : Execution.Scope) (code : Term) (stack : SourceAnnotatedRuntime.Stack)
    {dependencies : Dependencies} (plan : Plan dependencies)
    {receiving : SourceDependencyCapture.Scope} {hints : SourceContextualHints.Hints receiving} (forest : Forest hints)
    (output : Value) (demand : List Nat) (row : Footprint)
    (evidence : DeclarationEvidence := recipeEvidence) : Prop where
  | checked
      (current : Expression operations policy contracts world allowed scope (fun _ => none)
        code input currentDemand currentRequirements (signature plan))
      (scopeTyped : ScopedPorts.EffectScope contracts.erase.erase.ports scope ticket)
      (pending : SourceAnnotatedRuntimeTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward
        (OwnerPhaseTransitions.available (ownedTickets stack.erase)) world
        stack input output pendingDemand pendingRequirements resumes forest .nil allowed [])
      (closing : DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world stack.erase disposals)
      (templates : SourceAnnotatedClosingRecords.Records operations policy contracts tables annotations world stack disposals)
      (matched : SourceScheduledSavedPlans.Matches annotations forest)
      (contextual : SourceScheduledChecks.Local outward actions (OwnerPhaseTransitions.available (ownedTickets stack.erase)) world plan forest)
      (unique : (ownedTickets stack.erase).Nodup)
      (evaluated : RecursiveRequirements.Checked (resumes ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack.erase))
        (.sequence (currentRequirements.prepend (OwnerPhases.ofStack tables stack.erase)) pendingRequirements) row)
      (accepted : checkFootprint outside row = true)
      (accounting : demand = currentDemand ++ pendingDemand) :
      AtPlan operations policy contracts tables families required actions annotations world outward outside scope code stack plan forest output demand row evidence

inductive State [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy] (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (families : SourceDependencyFrames.Families)
    (required : SourceContextualRechecking.Required) (actions : Syntax.UsageTickets) (annotations : Annotations)
    (world : List Nat) (outward : List Instance) (outside : ProtectionContracts.Context)
    (scope : Execution.Scope) (code : Term) (stack : SourceAnnotatedRuntime.Stack)
    {receiving : SourceDependencyCapture.Scope} {hints : SourceContextualHints.Hints receiving} (forest : Forest hints)
    (output : Value) (demand : List Nat) (row : Footprint)
    (evidence : DeclarationEvidence := recipeEvidence) : Prop where
  | checked {plan : Plan dependencies}
      (current : Expression operations policy contracts world allowed scope (fun _ => none)
        code input currentDemand currentRequirements (signature plan))
      (scopeTyped : ScopedPorts.EffectScope contracts.erase.erase.ports scope ticket)
      (pending : SourceAnnotatedRuntimeTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward
        (OwnerPhaseTransitions.available (ownedTickets stack.erase)) world
        stack input output pendingDemand pendingRequirements resumes forest .nil allowed [])
      (closing : DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world stack.erase disposals)
      (templates : SourceAnnotatedClosingRecords.Records operations policy contracts tables annotations world stack disposals)
      (matched : SourceScheduledSavedPlans.Matches annotations forest)
      (contextual : SourceScheduledChecks.Local outward actions (OwnerPhaseTransitions.available (ownedTickets stack.erase)) world plan forest)
      (unique : (ownedTickets stack.erase).Nodup)
      (evaluated : RecursiveRequirements.Checked (resumes ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack.erase))
        (.sequence (currentRequirements.prepend (OwnerPhases.ofStack tables stack.erase)) pendingRequirements) row)
      (accepted : checkFootprint outside row = true)
      (accounting : demand = currentDemand ++ pendingDemand) :
      State operations policy contracts tables families required actions annotations world outward outside scope code stack forest output demand row evidence

/-- Forgetting the explicit plan recovers the existing shared invariant. -/
theorem AtPlan.state
    (state : AtPlan operations policy contracts tables families required actions annotations world outward outside
      scope code stack plan forest output demand row evidence) :
    State operations policy contracts tables families required actions annotations world outward outside
      scope code stack forest output demand row evidence := by
  cases state with
  | checked current scope pending closing templates matched contextual unique evaluated accepted accounting =>
      exact .checked current scope pending closing templates matched contextual unique evaluated accepted accounting

/-- Expose the existing current-plan witness without choosing a new source
or weakening any of its structural premises. -/
theorem State.atPlan
    (state : State operations policy contracts tables families required actions annotations world outward outside
      scope code stack forest output demand row evidence) :
    ∃ dependencies, ∃ plan : Plan dependencies,
      AtPlan operations policy contracts tables families required actions annotations world outward outside
        scope code stack plan forest output demand row evidence := by
  cases state with
  | checked current scope pending closing templates matched contextual unique evaluated accepted accounting =>
      exact ⟨_, _, .checked current scope pending closing templates matched contextual unique evaluated accepted accounting⟩

/-- Erasure constructs the old invariant from the same current and saved
source choices, rather than conjoining an independently selected derivation. -/
theorem State.erase
    (state : State operations policy contracts tables families required actions annotations world outward outside
      scope code stack forest output demand row evidence) :
    SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
      scope code.erase stack.erase forest output demand row evidence := by
  cases state with
  | checked current scope pending closing templates matched contextual unique evaluated accepted accounting =>
      exact .checked current.erase scope pending.erase closing templates.erase matched contextual unique evaluated accepted accounting

/-- Initial programs have no saved continuations or stored closing templates.
Their current source and capability checks are still explicit admission data. -/
theorem AtPlan.initial {plan : Plan dependencies}
    (current : Expression operations policy contracts world [] .none (fun _ => none) code output demand requirements (signature plan))
    (empty : demand = [])
    (contextual : SourceScheduledChecks.Local outward actions (OwnerPhaseTransitions.available []) world plan .nil)
    (evaluated : RecursiveRequirements.Checked [] [] (OwnerPhaseTransitions.available []) requirements row)
    (accepted : checkFootprint outside row = true) :
    AtPlan operations policy contracts tables families required actions annotations world outward outside
      .none code .nil plan .nil output demand row evidence := by
  subst demand
  have currentCheck := RecursiveRequirements.checked_prepend_iff.mpr
    (show RecursiveRequirements.Checked [] ([] ++ []) (OwnerPhaseTransitions.available []) requirements row from evaluated)
  have pendingCheck : RecursiveRequirements.Checked [] [] (OwnerPhaseTransitions.available []) (Requirements.request [] []) [] := .request rfl
  simpa only [List.append_nil] using
    (AtPlan.checked (evidence := evidence) (tables := tables) current .none (.nil (List.Subset.refl [])) .nil .nil .nil
      contextual (by decide) (RecursiveRequirements.Checked.sequence currentCheck pendingCheck)
      (by simpa only [List.append_nil] using accepted) rfl)

theorem initial {plan : Plan dependencies}
    (current : Expression operations policy contracts world [] .none (fun _ => none) code output demand requirements (signature plan))
    (empty : demand = [])
    (contextual : SourceScheduledChecks.Local outward actions (OwnerPhaseTransitions.available []) world plan .nil)
    (evaluated : RecursiveRequirements.Checked [] [] (OwnerPhaseTransitions.available []) requirements row)
    (accepted : checkFootprint outside row = true) :
    State operations policy contracts tables families required actions annotations world outward outside
      .none code .nil .nil output demand row evidence :=
  (AtPlan.initial current empty contextual evaluated accepted).state

/-- Source replacement keeps the exact pending source, stores and annotations.
Only present expression typing, contextual checking and evaluation are needed. -/
theorem AtPlan.replace_current
    {requirements : Requirements currentDemand} {plan : Plan dependencies}
    (current : Expression operations policy contracts world allowed nextScope (fun _ => none)
      next input currentDemand reduced (signature plan))
    (scopeTyped : ScopedPorts.EffectScope contracts.erase.erase.ports nextScope ticket)
    (pending : SourceAnnotatedRuntimeTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward
      (OwnerPhaseTransitions.available (ownedTickets stack.erase)) world
      stack input output pendingDemand pendingRequirements resumes forest .nil allowed [])
    (closing : DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world stack.erase disposals)
    (templates : SourceAnnotatedClosingRecords.Records operations policy contracts tables annotations world stack disposals)
    (matched : SourceScheduledSavedPlans.Matches annotations forest)
    (contextual : SourceScheduledChecks.Local outward actions (OwnerPhaseTransitions.available (ownedTickets stack.erase)) world plan forest)
    (unique : (ownedTickets stack.erase).Nodup)
    (evaluated : RecursiveRequirements.Checked (resumes ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack.erase))
      (.sequence (requirements.prepend (OwnerPhases.ofStack tables stack.erase)) pendingRequirements) row)
    (accepted : checkFootprint outside row = true)
    (accounting : demand = currentDemand ++ pendingDemand)
    (same : ∀ store receiving before, RecursiveRequirements.evaluate store receiving before reduced =
      RecursiveRequirements.evaluate store receiving before requirements) :
    AtPlan operations policy contracts tables families required actions annotations world outward outside nextScope next stack plan forest output demand row evidence := by
  apply AtPlan.checked current scopeTyped pending closing templates matched contextual unique _ accepted accounting
  apply RecursiveRequirements.evaluate_sound
  have original := RecursiveRequirements.checked_complete evaluated
  simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend] at original ⊢
  rw [same]
  exact original

theorem replace_current
    {requirements : Requirements currentDemand} {plan : Plan dependencies}
    (current : Expression operations policy contracts world allowed nextScope (fun _ => none)
      next input currentDemand reduced (signature plan))
    (scopeTyped : ScopedPorts.EffectScope contracts.erase.erase.ports nextScope ticket)
    (pending : SourceAnnotatedRuntimeTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward
      (OwnerPhaseTransitions.available (ownedTickets stack.erase)) world
      stack input output pendingDemand pendingRequirements resumes forest .nil allowed [])
    (closing : DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world stack.erase disposals)
    (templates : SourceAnnotatedClosingRecords.Records operations policy contracts tables annotations world stack disposals)
    (matched : SourceScheduledSavedPlans.Matches annotations forest)
    (contextual : SourceScheduledChecks.Local outward actions (OwnerPhaseTransitions.available (ownedTickets stack.erase)) world plan forest)
    (unique : (ownedTickets stack.erase).Nodup)
    (evaluated : RecursiveRequirements.Checked (resumes ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack.erase))
      (.sequence (requirements.prepend (OwnerPhases.ofStack tables stack.erase)) pendingRequirements) row)
    (accepted : checkFootprint outside row = true)
    (accounting : demand = currentDemand ++ pendingDemand)
    (same : ∀ store receiving before, RecursiveRequirements.evaluate store receiving before reduced =
      RecursiveRequirements.evaluate store receiving before requirements) :
    State operations policy contracts tables families required actions annotations world outward outside nextScope next stack forest output demand row evidence :=
  (AtPlan.replace_current current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting same).state

/-- Bind reduction keeps the same body plan, pending source and saved map.
The existing source substitution and requirement-evaluation lemmas do the work. -/
theorem bind_preserves_bounds {plan : Plan dependencies}
    (bounds : Annotation world plan)
    (state : AtPlan operations policy contracts tables families required actions annotations world outward outside scope
      (.bind hint parameter value body) stack plan forest output demand row evidence)
    (closed : ClosedValue value.erase) :
    ∃ nextDependencies, ∃ nextPlan : Plan nextDependencies, ∃ nextBounds : Annotation world nextPlan,
      AtPlan operations policy contracts tables families required actions annotations world outward outside scope
      (body.subst parameter value) stack nextPlan forest output demand row evidence ∧
      Reduced world .bind bounds nextBounds := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
    rename_i allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals
    have originalCurrent := current
    generalize sameSignature : signature plan = currentSignature at current
    cases current with
    | checked hint metadata node => cases node with
      | bind initializer body =>
        cases plan with
        | sequence initialPlan bodyPlan =>
          obtain ⟨reduced, replacement, same⟩ := SourceAnnotatedSources.bind_expression originalCurrent closed
          cases contextual with
          | sequence first second =>
            exact ⟨_, bodyPlan, bounds.second,
              AtPlan.replace_current replacement scopeTyped pending closing templates matched second unique evaluated accepted accounting same, .bind bounds⟩


/-- Beta reduction reuses the actual latent body plan and its check. Its empty
lexical ticket scope is derived by the existing source substitution theorem. -/
theorem beta_preserves_bounds {plan : Plan dependencies}
    (bounds : Annotation world plan)
    (state : AtPlan operations policy contracts tables families required actions annotations world outward outside scope
      (.app hint (.lambda functionHint parameter body) value) stack plan forest output demand row evidence)
    (closed : ClosedValue value.erase) :
    ∃ nextDependencies, ∃ nextPlan : Plan nextDependencies, ∃ nextBounds : Annotation world nextPlan,
      AtPlan operations policy contracts tables families required actions annotations world outward outside .none
      (body.subst parameter value) stack nextPlan forest output demand row evidence ∧
      Reduced world .beta bounds nextBounds := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
    rename_i allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals
    have originalCurrent := current
    generalize sameSignature : signature plan = currentSignature at current
    cases current with
    | checked hint metadata node => cases node with
      | app function argument admitted =>
        cases plan with
        | sequence functionPlan rest => cases rest with
          | sequence argumentPlan bodyPlan =>
            obtain ⟨reduced, replacement, same⟩ := SourceAnnotatedSources.beta_expression originalCurrent closed
            cases contextual with
            | sequence first rest => cases rest with
              | sequence argument body =>
                exact ⟨_, bodyPlan, bounds.second.second,
                  AtPlan.replace_current replacement .none pending closing templates matched body unique evaluated accepted accounting same, .beta bounds⟩

theorem bind_preserves
    (state : State operations policy contracts tables families required actions annotations world outward outside scope
      (.bind hint parameter value body) stack forest output demand row evidence)
    (closed : ClosedValue value.erase) :
    State operations policy contracts tables families required actions annotations world outward outside scope
      (body.subst parameter value) stack forest output demand row evidence := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
      obtain ⟨_, _, _, next, _⟩ := bind_preserves_bounds .absent
        (.checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting) closed
      exact next.state

theorem beta_preserves
    (state : State operations policy contracts tables families required actions annotations world outward outside scope
      (.app hint (.lambda functionHint parameter body) value) stack forest output demand row evidence)
    (closed : ClosedValue value.erase) :
    State operations policy contracts tables families required actions annotations world outward outside .none
      (body.subst parameter value) stack forest output demand row evidence := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting =>
      obtain ⟨_, _, _, next, _⟩ := beta_preserves_bounds .absent
        (.checked current scopeTyped pending closing templates matched contextual unique evaluated accepted accounting) closed
      exact next.state


end

end Ash.OneShot.SourceAnnotatedRuntimeState

#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.State.erase

#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.initial

#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.replace_current

#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.bind_preserves

#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.beta_preserves

#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.AtPlan.state

#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.AtPlan.initial

#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.AtPlan.replace_current
#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.bind_preserves_bounds
#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.beta_preserves_bounds

#print axioms Ash.OneShot.SourceAnnotatedRuntimeState.State.atPlan
