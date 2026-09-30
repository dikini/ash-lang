import SourceScheduledRegistries

/-! Handler entry registers the source declaration and its structural recipe
together. Existing activation relocation supplies the requirement evaluation;
the actual body and pending plans remain the same. -/
namespace Ash.OneShot.SourceScheduledHandlers
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements Checked)
open RecursiveHandlerTables (context_congr registered_lookup checked_activation)
open SourcePlanSignatures (signature)
open SourceRetainedPlans (Forest)

def register {α : Type} (registry : HandlerData → α) (activation : Nat) (entry : α) : HandlerData → α :=
  fun handler => if handler.activation = activation then entry else registry handler

theorem register_agrees {registry : HandlerData → α} {stack : Stack}
    (fresh : activation ∉ stack.erase.activations) :
    ∀ handler, handler.activation ∈ stack.erase.activations →
      registry handler = register registry activation entry handler := by
  intro handler member
  have different : handler.activation ≠ activation := fun same => fresh (same ▸ member)
  simp only [register, if_neg different]

theorem handler_annotations
    (state : SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
      scope (.handle requested code clauses) stack forest output demand row)
    (retained : stack.erase.activations ⊆ history) :
    ∃ answerPort : ScopedPorts.Port, ∃ table clauseFamilies declarationRequirements,
    ∀ activation answerType, activation ∉ history → ScopedPorts.eraseType answerType = answerPort →
    ∃ handler : HandlerData, ∃ nextForest : SourceScheduledSavedPlans.Saved,
      handler.activation = activation ∧ handler.answer = answerType ∧
      RawStep ⟨.handle requested code clauses, scope, stack⟩
        ⟨code, scope, .push (.handler handler) stack⟩ [] [] ∧
      SourceScheduledState.State operations policy contracts (RecursiveHandlerTables.register tables handler.activation table)
        (register families handler.activation clauseFamilies) (register required handler.activation declarationRequirements)
        actions annotations world outward outside scope code (.push (.handler handler) stack) nextForest.forest output demand row := by
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique checked accepted accounting =>
    rename_i dependencies allowed answer bodyDemand currentRequirements ticket tailDemand tailRequirements resumes disposals plan
    generalize signatureSame : signature plan = currentSignature at current
    cases current with
    | handler bodySource clausesTyped capabilities coverage clauseUnique admitted table modes declarations =>
      cases plan with
      | handler declarationRequirements plans bodyPlan =>
        obtain ⟨rfl, clausesSame, bodySame⟩ := SourcePlanSignatures.Signature.handler.inj signatureSame
        rw [← bodySame] at bodySource
        cases contextual with
        | handler recipes certified supplied bodyCheck =>
          have actualRecipes := recipes.signature_congr clausesSame
          obtain ⟨bodyRow, tailRow, currentCheck, tailCheck, sameRow⟩ :=
            RecursiveRequirements.checked_sequence_parts checked
          have checkedBody := RecursiveRequirements.checked_prepend_iff.mp
            (RecursiveRequirements.checked_prepend_iff.mp currentCheck)
          simp only [List.append_nil, List.cons_append, List.nil_append] at checkedBody
          rename_i sourceFamilies effect residual bodyDep bodySignature sourcePlans bodyRequirements planClauses
          refine ⟨answer.erase.erase.port, table, sourceFamilies, declarationRequirements, ?_⟩
          intro activation answerType fresh answerSame
          let handler : HandlerData := ⟨activation, effect, clauses, scope, answerType,
            ScopedPorts.clauses_have_ticket_barrier clausesTyped⟩
          let nextTables := RecursiveHandlerTables.register tables activation table
          let nextFamilies := register families activation sourceFamilies
          let nextRequired := register required activation declarationRequirements
          have freshStack : activation ∉ stack.erase.activations := fun member => fresh (retained member)
          have tablesAgree : ∀ actual, actual.activation ∈ stack.erase.activations → tables actual = nextTables actual :=
            RecursiveHandlerTables.register_agrees freshStack
          have familiesAgree : ∀ actual, actual.activation ∈ stack.erase.activations → families actual = nextFamilies actual :=
            register_agrees freshStack
          have requiredAgree : ∀ actual, actual.activation ∈ stack.erase.activations → required actual = nextRequired actual :=
            register_agrees freshStack
          have sameContext := context_congr tablesAgree
          have installed : nextTables handler = table := registered_lookup rfl
          have frame : SourceScheduledFrames.Frame operations policy contracts nextTables nextFamilies nextRequired outward actions
              (OwnerPhaseTransitions.available (ownedTickets stack)) world (forest.append .nil)
              (.handler handler) answer answer [] (.request [] [])
              (.handler effect table sourceFamilies) (fun rest => .handler declarationRequirements rest) (fun rest => .handler rest)
              (effect :: residual) residual := by
            have base : SourceScheduledFrames.Frame operations policy contracts (fun _ => table) (fun _ => sourceFamilies)
                (fun _ => declarationRequirements) outward actions (OwnerPhaseTransitions.available (ownedTickets stack)) world
                (forest.append .nil) (.handler handler) answer answer [] (.request [] [])
                (.handler effect table sourceFamilies) (fun rest => .handler declarationRequirements rest) (fun rest => .handler rest)
                (effect :: residual) residual :=
              .handler ⟨_, scopeTyped⟩ (by simp only [handler, answerSame])
                clausesTyped coverage clauseUnique declarations actualRecipes
                (by simpa only [SourceDependencyProjection.scope_append_nil] using supplied) capabilities modes
            apply base.registries_congr
            all_goals intro actual member
            all_goals change actual.activation ∈ [activation] at member
            all_goals have same := List.mem_singleton.mp member
            all_goals simp only [nextTables, nextFamilies, nextRequired, RecursiveHandlerTables.register, register, same, if_true]
          have pendingAfter := SourceScheduledFrames.Segment.push frame
            ((pending.registries_congr tablesAgree familiesAgree requiredAgree).input_weaken admitted) (List.Subset.refl _)
          have active : Checked (resumes ++ disposals) (OwnerPhases.ofStack nextTables (.push (.handler handler) stack))
              (OwnerPhaseTransitions.available (ownedTickets stack)) bodyRequirements bodyRow := by
            have relocated := checked_activation checkedBody (front := []) (tail := OwnerPhases.ofStack tables stack)
              (second := activation) rfl
            simpa only [List.nil_append, OwnerPhases.ofStack, OwnerPhases.frameEntry, installed, handler, sameContext]
              using relocated
          have afterBody : Checked (resumes ++ disposals) []
              (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets stack)) bodyDemand)
              (.sequence ((Requirements.request [] []).prepend (OwnerPhases.ofStack nextTables stack)) tailRequirements) tailRow :=
            .sequence (firstRow := []) (secondRow := tailRow)
              (.request (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])) tailCheck
          have prefixed := RecursiveRequirements.checked_prepend_iff.mpr
            (show Checked (resumes ++ disposals) (OwnerPhases.ofStack nextTables (.push (.handler handler) stack) ++ [])
              (OwnerPhaseTransitions.available (ownedTickets stack)) bodyRequirements bodyRow from by
                simpa only [List.append_nil] using active)
          have templatesAfter := (templates.tables_congr (nextTables := nextTables)).transport (nextRoot := .push (.handler handler) stack)
            (fun _ _ known => known) (fun _ _ known => known) (fun _ _ located => .push located)
          refine ⟨handler, ⟨_, _, .handler (effect := effect) (table := table) (families := sourceFamilies) (required := declarationRequirements) forest⟩, rfl, rfl, .enterHandler handler code stack, ?_⟩
          rw [sameRow]
          exact .checked bodySource scopeTyped pendingAfter (.push (DeclaredSourceClosing.records_congr closing))
            templatesAfter (.handler matched) bodyCheck unique (.sequence prefixed afterBody) (sameRow ▸ accepted)
            (by simpa only [List.nil_append] using accounting)

theorem handler_preserves
    (state : SourceScheduledState.State operations policy contracts tables families required actions annotations world outward outside
      scope (.handle requested code clauses) stack forest output demand row)
    (retained : stack.erase.activations ⊆ history) :
    ∃ handler : HandlerData, ∃ table clauseFamilies declarationRequirements, ∃ nextForest : SourceScheduledSavedPlans.Saved,
      handler.activation ∉ history ∧
      RawStep ⟨.handle requested code clauses, scope, stack⟩
        ⟨code, scope, .push (.handler handler) stack⟩ [] [] ∧
      SourceScheduledState.State operations policy contracts (RecursiveHandlerTables.register tables handler.activation table)
        (register families handler.activation clauseFamilies) (register required handler.activation declarationRequirements)
        actions annotations world outward outside scope code (.push (.handler handler) stack) nextForest.forest output demand row := by
  obtain ⟨answerPort, table, clauseFamilies, declarationRequirements, admitted⟩ := handler_annotations state retained
  obtain ⟨activation, fresh⟩ := ScopedTyping.fresh_world_name history
  obtain ⟨handler, saved, activationSame, _, raw, next⟩ :=
    admitted activation (ScopedPorts.embedPort answerPort) fresh (by simp)
  exact ⟨handler, table, clauseFamilies, declarationRequirements, saved, activationSame ▸ fresh, raw, next⟩

end Ash.OneShot.SourceScheduledHandlers

#print axioms Ash.OneShot.SourceScheduledHandlers.register_agrees
#print axioms Ash.OneShot.SourceScheduledHandlers.handler_annotations
#print axioms Ash.OneShot.SourceScheduledHandlers.handler_preserves
