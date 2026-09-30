import DeclaredSharedCleanup

/-! Resource entry shares the source-selected body annotation with its new
cell provider and surviving caller. Existing finite requirement checking chooses
the fresh identity; source, result and runtime proofs use that same identity.
-/
namespace Ash.OneShot.DeclaredSourceInterfaces
open ScopedExpressions ScopedExecution CoherentSourceTypes
open RecursiveRequirements (Requirements Checked evaluate)
open OwnerPhaseTransitions (available spendAll)

theorem resource_state
    (state : State operations policy contracts tables actions world outside scope
      (.resource binder initializer body) stack output demand row)
    (isValue : initializer.IsValue) :
    ∃ identity payload answer,
      identity ∉ world ∧ initializer = .integer payload ∧
      RawStep ⟨.resource binder initializer body, scope, stack⟩
        ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
          .push (.cell identity payload scope answer) stack⟩ [.resource identity] [] ∧
      State operations policy contracts tables actions (world ++ [identity]) outside scope
        (body.instantiate (Instantiation.Environment.empty.bind binder identity))
        (.push (.cell identity payload scope answer) stack) output demand row := by
  cases state with
  | checked current scopeTyped pending closing unique checked accepted accounting connected =>
      subst demand
      rename_i allowed input currentDemand currentRequirements ticket pendingDemand pendingRequirements resumes disposals
      obtain ⟨payload, outward, same, openings, evaluation⟩ :=
        DeclaredSourceEntries.resource_parts current isValue
      subst initializer
      obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, rfl⟩ :=
        RecursiveRequirements.checked_sequence_parts checked
      have currentAt := RecursiveRequirements.checked_prepend_iff.mp currentCheck
      simp only [List.append_nil] at currentAt
      have outwardCheck := RecursiveRequirements.evaluate_sound ((evaluation _ _ _).symm.trans
        (RecursiveRequirements.checked_complete currentAt))
      obtain ⟨forbidden, preserved⟩ := ResourceRequirements.checked_open_resource outwardCheck
      obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name (world ++ forbidden)
      have freshWorld : identity ∉ world := fun member => fresh (List.mem_append_left _ member)
      obtain ⟨requests, opened, bodySource, hidden, noEscape, admitted⟩ := openings identity freshWorld
      have bodyChecked := preserved identity (fun member => fresh (List.mem_append_right _ member)) opened hidden
      let answer := ScopedPorts.embedPort input.port
      have frame : DeclaredSourceFrames.Frame operations policy contracts tables (world ++ [identity])
          (.cell identity payload scope answer) input input [] (.request [] []) :=
        .cell ⟨_, ScopedPorts.effect_scope_has_types scopeTyped⟩
          (by simpa only [answer, ScopedPorts.erase_embed_port] using noEscape)
          (by simp only [answer, ScopedPorts.erase_embed_port])
      have effectFrame : ScopedPorts.EffectFrame operations.ports contracts.ports (world ++ [identity])
          (.cell identity payload scope answer) (.cell identity :: allowed) allowed :=
        .cell ⟨_, scopeTyped⟩ (by simpa only [answer, ScopedPorts.erase_embed_port] using noEscape)
      have ready := ScopedPorts.typed_resource_closed
        (SourceTemplates.expression_ports (DeclaredSources.expression_erase current) scopeTyped)
      refine ⟨identity, payload, answer, freshWorld, rfl,
        .enterCell binder identity payload body scope answer stack ready, ?_⟩
      refine .checked bodySource scopeTyped
        (DeclaredSourceFrames.push frame
          (DeclaredSourceFrames.segment_world_weaken pending (List.subset_append_left _ _)))
        (.push (DeclaredSourceClosing.records_world_weaken closing (List.subset_append_left _ _)))
        unique ?_ accepted rfl
        (.push effectFrame (ScopedActionInterfaces.world_weaken connected (List.subset_append_left _ _)) admitted)
      apply RecursiveRequirements.evaluate_sound
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        OwnerPhases.ofStack, OwnerPhases.frameEntry, List.append_nil,
        RecursiveRecomposition.evaluate_empty, RecursiveRecomposition.merge_empty_left, ownedTickets, spendAll]
      rw [RecursiveRequirements.checked_complete bodyChecked, RecursiveRequirements.checked_complete pendingCheck]
      rfl

theorem resource_progress
    (before : Run operations declarations policy registry tables
      ⟨⟨⟨.resource binder initializer body, scope, stack⟩, issued, completed⟩, activations⟩ output demand row bound)
    (isValue : initializer.IsValue) :
    ∃ identity payload answer,
      initializer = .integer payload ∧
      let state : NamedState := ⟨⟨⟨.resource binder initializer body, scope, stack⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) stack⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [.resource identity] []) ∧
      Run operations declarations policy registry tables
        (ScopedPortJoint.advanceState state after [.resource identity] []) output demand row bound := by
  obtain ⟨actions, usage, history, shared, retained⟩ := before.actions
  obtain ⟨identity, payload, answer, fresh, same, raw, next⟩ := resource_state shared isValue
  subst initializer
  have results := (CompletionFrames.resource_step before.current.results fresh (answer := answer)).2
  have absent : Owner.resource identity ∉ issued :=
    fun member => fresh (ScopedTyping.mem_resource_world.mpr member)
  have unique : issued.Nodup := before.current.ledger.2
  have freshOwners : (issued ++ [Owner.resource identity]).Nodup := by
    apply List.nodup_append.mpr ⟨unique, by simp, ?_⟩
    intro old present new singleton sameOwner
    simp only [List.mem_singleton] at singleton
    subst new
    subst old
    exact absent present
  have checks : AccessChecks ⟨.resource binder (.integer payload) body, scope, stack⟩ [] :=
    ScopedPortJoint.ordinary_access_checks (by simp [Code.IsValue])
      (by intro requested operation operand impossible; cases impossible) (by intro binder impossible; cases impossible)
  have freshHandlers : (activations ++ enteredActivations
      ⟨.resource binder (.integer payload) body, scope, stack⟩
      ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) stack⟩).Nodup := by
    simpa [enteredActivations] using before.current.names.unique
  refine ⟨identity, payload, answer, rfl, ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩, ?_⟩
  apply assemble_entry before.current raw freshOwners freshHandlers checks usage history retained
  · simpa [ScopedActionUsage.advance, ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using next
  · simpa [ScopedTyping.resource_world_append, ScopedTyping.resourceWorld] using results
  · rfl
  · simp

end Ash.OneShot.DeclaredSourceInterfaces

#print axioms Ash.OneShot.DeclaredSourceInterfaces.resource_state
#print axioms Ash.OneShot.DeclaredSourceInterfaces.resource_progress
