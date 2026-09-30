import DeclaredSharedResources

/-! Handler entry retains the same residual effect annotation in its source
body, declarations, installed frame and surviving caller. The existing fresh
activation and requirement-relocation construction is unchanged.
-/
namespace Ash.OneShot.DeclaredSourceInterfaces
open ScopedExpressions ScopedExecution CoherentSourceTypes
open RecursiveRequirements (Requirements Checked)
open RecursiveHandlerTables (register register_agrees context_congr registered_lookup checked_activation)

theorem handler_state
    (state : State operations policy contracts tables actions world outside scope
      (.handle requested code clauses) stack output demand row)
    (retained : stack.erase.activations ⊆ history) :
    ∃ handler : HandlerData, ∃ table,
      handler.activation ∉ history ∧
      register tables handler.activation table handler = table ∧
      RawStep ⟨.handle requested code clauses, scope, stack⟩
        ⟨code, scope, .push (.handler handler) stack⟩ [] [] ∧
      State operations policy contracts (register tables handler.activation table) actions world outside
        scope code (.push (.handler handler) stack) output demand row := by
  cases state with
  | checked current scopeTyped pending closing unique checked accepted accounting connected =>
      subst demand
      rename_i allowed answer bodyDemand currentRequirements ticket tailDemand tailRequirements resumes disposals
      obtain ⟨effect, residual, table, bodyRequirements, rfl, rfl, body, clausesTyped, capabilities,
        coverage, clauseUnique, admitted, modes, declarations⟩ := DeclaredSources.handler_parts current
      have environmentSame : Environment.empty.ports = ScopedPorts.TypeEnv.empty := by
        funext name
        rfl
      rw [environmentSame] at clausesTyped
      obtain ⟨bodyRow, tailRow, currentCheck, tailCheck, sameRow⟩ :=
        RecursiveRequirements.checked_sequence_parts checked
      have bodyCheck := RecursiveRequirements.checked_prepend_iff.mp
        (RecursiveRequirements.checked_prepend_iff.mp currentCheck)
      simp only [List.append_nil, List.cons_append, List.nil_append] at bodyCheck
      obtain ⟨activation, fresh⟩ := ScopedTyping.fresh_world_name history
      let handler : HandlerData := ⟨activation, effect, clauses, scope, ScopedPorts.embedPort answer.port,
        ScopedPorts.clauses_have_ticket_barrier clausesTyped⟩
      let next := register tables activation table
      have agree : ∀ actual, actual.activation ∈ stack.erase.activations → tables actual = next actual :=
        register_agrees (fun member => fresh (retained member))
      have sameContext := context_congr agree
      have installed : next handler = table := registered_lookup rfl
      have frame : DeclaredSourceFrames.Frame operations policy contracts
          (register tables handler.activation table) world (.handler handler) answer answer [] (.request [] []) :=
        .handler (.handler ⟨_, ScopedPorts.effect_scope_has_types scopeTyped⟩
          (by simpa only [handler, ScopedPorts.erase_embed_port] using clausesTyped) coverage clauseUnique)
          (by simp only [handler, ScopedPorts.erase_embed_port])
          (by
            change DeclaredSources.Declarations operations policy contracts world Environment.empty residual
              effect answer clauses (next handler)
            rw [installed]
            exact declarations) capabilities (by
            change SourceTemplates.ClauseModes clauses (next handler)
            rw [installed]
            exact modes)
      have effectFrame : ScopedPorts.EffectFrame operations.ports contracts.ports world
          (.handler handler) (effect :: residual) residual :=
        .handler ⟨_, scopeTyped⟩
          (by simpa only [handler, ScopedPorts.erase_embed_port] using clausesTyped) coverage clauseUnique
      have source := DeclaredSourceFrames.push frame
        (DeclaredSourceFrames.segment_tables_congr pending agree)
      have current : Checked (resumes ++ disposals) (OwnerPhases.ofStack next (.push (.handler handler) stack))
          (OwnerPhaseTransitions.available (ownedTickets stack)) bodyRequirements bodyRow := by
        have relocated := checked_activation bodyCheck (front := []) (tail := OwnerPhases.ofStack tables stack)
          (second := activation) rfl
        simpa only [List.nil_append, OwnerPhases.ofStack, OwnerPhases.frameEntry, installed, handler, sameContext]
          using relocated
      have afterBody : Checked (resumes ++ disposals) []
          (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets stack)) bodyDemand)
          (.sequence ((Requirements.request [] []).prepend (OwnerPhases.ofStack next stack)) tailRequirements) tailRow :=
        .sequence (firstRow := []) (secondRow := tailRow)
          (.request (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])) tailCheck
      have prefixed : Checked (resumes ++ disposals) [] (OwnerPhaseTransitions.available (ownedTickets stack))
          (bodyRequirements.prepend (OwnerPhases.ofStack next (.push (.handler handler) stack))) bodyRow :=
        RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [List.append_nil] using current)
      refine ⟨handler, table, fresh, installed, .enterHandler handler code stack, ?_⟩
      rw [sameRow]
      exact .checked body scopeTyped source (.push (DeclaredSourceClosing.records_congr closing)) unique
        (.sequence prefixed afterBody) (sameRow ▸ accepted) rfl
        (.push effectFrame (ScopedActionInterfaces.input_weaken connected admitted) (List.Subset.refl _))

theorem handler_progress
    (before : Run operations declarations policy registry tables
      ⟨⟨⟨.handle requested body clauses, scope, stack⟩, issued, completed⟩, activations⟩ output demand row bound) :
    ∃ (handler : HandlerData) (table : List (Nat × ProtectionContracts.ClauseContract)),
      handler.activation ∉ activations ∧
      let state : NamedState := ⟨⟨⟨.handle requested body clauses, scope, stack⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨body, scope, .push (.handler handler) stack⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] []) ∧
      Run operations declarations policy registry (register tables handler.activation table)
        (ScopedPortJoint.advanceState state after [] []) output demand row bound := by
  have retainedActivations : stack.erase.activations ⊆ activations := by
    intro activation member
    exact List.count_pos_iff.mp (Nat.lt_of_lt_of_le (List.count_pos_iff.mpr member)
      (before.current.names.handlers activation))
  obtain ⟨actions, usage, history, shared, retained⟩ := before.actions
  obtain ⟨handler, table, fresh, installed, raw, next⟩ := handler_state shared retainedActivations
  have results := DeclaredExecution.handler_step_results raw before.current.results ⟨requested, body, clauses, rfl⟩
  have checks : AccessChecks ⟨.handle requested body clauses, scope, stack⟩ [] :=
    ScopedPortJoint.ordinary_access_checks (by simp [Code.IsValue])
      (by intro requested operation operand impossible; cases impossible) (by intro binder impossible; cases impossible)
  have freshOwners : (issued ++ []).Nodup := by simpa [RunState.erase] using before.current.ledger.2
  have freshHandlers : (activations ++ enteredActivations ⟨.handle requested body clauses, scope, stack⟩
      ⟨body, scope, .push (.handler handler) stack⟩).Nodup := by
    change (activations ++ [handler.activation]).Nodup
    apply List.nodup_append.mpr ⟨before.current.names.unique, by simp, ?_⟩
    intro old present new singleton same
    simp only [List.mem_singleton] at singleton
    subst new
    subst old
    exact fresh present
  refine ⟨handler, table, fresh, ⟨.event _ _ _ _ raw freshOwners freshHandlers, checks⟩, ?_⟩
  apply assemble_entry before.current raw freshOwners freshHandlers checks usage history retained
  · simpa only [ScopedActionUsage.advance, List.append_nil] using next
  · simpa only [List.append_nil] using results
  · rfl
  · simp

end Ash.OneShot.DeclaredSourceInterfaces

#print axioms Ash.OneShot.DeclaredSourceInterfaces.handler_state
#print axioms Ash.OneShot.DeclaredSourceInterfaces.handler_progress
