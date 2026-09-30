import SourceAnnotatedRuntimeEntries
import SourceStructuralHandlerEntry
import SourceBoundHandlerEntry

/-! Handler registration preserves the actual annotated pending source where
registry entries agree at retained activations, including dormant captures. -/
namespace Ash.OneShot.SourceAnnotatedRuntimeTyping

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
open ScopedExpressions ScopedExecution

theorem Frame.registries_congr
    (frame : Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world receiving
      entry input output demand requirements layer decorate decoratePlans incoming outgoing)
    (tablesAgree : ∀ handler, handler.activation ∈ entry.erase.erase.activation → tables handler = nextTables handler)
    (familiesAgree : ∀ handler, handler.activation ∈ entry.erase.erase.activation → families handler = nextFamilies handler)
    (requiredAgree : ∀ handler, handler.activation ∈ entry.erase.erase.activation → required handler = nextRequired handler) :
    Frame (evidence := evidence) operations policy contracts nextTables nextFamilies nextRequired outward actions phases world receiving
      entry input output demand requirements layer decorate decoratePlans incoming outgoing := by
  cases frame with
  | plain context hint closed scope inputAnnotation outputAnnotation checked => exact .plain context hint closed scope inputAnnotation outputAnnotation checked
  | handler scope annotation clauses coverage unique declarations recipes supplied capabilities modes =>
      have tableSame := tablesAgree _ List.mem_cons_self
      have familiesSame := familiesAgree _ List.mem_cons_self
      have requiredSame := requiredAgree _ List.mem_cons_self
      rename_i handler plans
      generalize oldFamily : families handler.erase = family at *
      generalize oldTable : tables handler.erase = table at *
      generalize oldRequired : required handler.erase = needed at *
      clear oldFamily oldTable oldRequired
      subst family table needed
      exact .handler scope annotation clauses coverage unique declarations recipes supplied capabilities modes
  | cell scope noEscape annotation interface => exact .cell scope noEscape annotation interface
  | armed scope callback annotation interface checked => exact .armed scope callback annotation interface checked
  | running scope callback saved annotation interface => exact .running scope callback saved annotation interface
  | closing scope interface => exact .closing scope interface
  | retiring known interface => exact .retiring known interface

theorem Segment.registries_congr
    (segment : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records forest outside incoming outgoing)
    (tablesAgree : ∀ handler, handler.activation ∈ stack.erase.erase.activations → tables handler = nextTables handler)
    (familiesAgree : ∀ handler, handler.activation ∈ stack.erase.erase.activations → families handler = nextFamilies handler)
    (requiredAgree : ∀ handler, handler.activation ∈ stack.erase.erase.activations → required handler = nextRequired handler) :
    Segment (evidence := evidence) operations policy contracts nextTables nextFamilies nextRequired actions outward phases world
      stack input output demand requirements records forest outside incoming outgoing := by
  induction segment with
  | nil bound => exact .nil bound
  | push head tail bound ih =>
      have nextTablesAgree := fun handler member => tablesAgree handler (List.mem_append_right _ member)
      have same := RecursiveHandlerTables.context_congr nextTablesAgree
      have changed := head.registries_congr
        (fun handler member => tablesAgree handler (List.mem_append_left _ member))
        (fun handler member => familiesAgree handler (List.mem_append_left _ member))
        (fun handler member => requiredAgree handler (List.mem_append_left _ member))
      simpa only [same] using Segment.push changed (ih nextTablesAgree
        (fun handler member => familiesAgree handler (List.mem_append_right _ member))
        (fun handler member => requiredAgree handler (List.mem_append_right _ member))) bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live known actionKnown inputAnnotation answerAnnotation scope held
        (ihSaved
          (fun handler member => tablesAgree handler (List.mem_append_left _ member))
          (fun handler member => familiesAgree handler (List.mem_append_left _ member))
          (fun handler member => requiredAgree handler (List.mem_append_left _ member))) savedBound
        (ihTail
          (fun handler member => tablesAgree handler (List.mem_append_right _ member))
          (fun handler member => familiesAgree handler (List.mem_append_right _ member))
          (fun handler member => requiredAgree handler (List.mem_append_right _ member))) resume close bound
  | spent known annotation scope tail bound ih =>
      exact .spent known annotation scope (ih tablesAgree familiesAgree requiredAgree) bound

theorem Segment.input_weaken
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records hints outside incoming outgoing)
    (smaller : nextIncoming ⊆ incoming) :
    Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records hints outside nextIncoming outgoing := by
  cases source with
  | nil bound => exact .nil (List.Subset.trans smaller bound)
  | push head tail bound => exact .push head tail (List.Subset.trans smaller bound)
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound =>
      exact .live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close
        (List.Subset.trans smaller bound)
  | spent known annotation scope tail bound => exact .spent known annotation scope tail (List.Subset.trans smaller bound)

end Ash.OneShot.SourceAnnotatedRuntimeTyping

namespace Ash.OneShot.SourceAnnotatedRuntimeHandlers

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  {evidence : SourcePlannedFrames.DeclarationEvidence}
  [SourceStructuralHandlerEntry.DeclarationRetention admission evidence outward]
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements Checked)
open RecursiveHandlerTables (context_congr registered_lookup checked_activation)
open SourceScheduledHandlers (register register_agrees)
open SourcePlanSignatures (signature)
open SourceRetainedPlans (Forest)

theorem handler_annotations_exact_snapshot
    (snapshot : SourceBoundSnapshots.Snapshot world)
    (state : SourceAnnotatedRuntimeState.AtPlan operations policy contracts tables families required actions annotations world outward outside
      scope (.handle hint requested code clauses) stack snapshot.plan snapshot.forest output demand row evidence)
    (retained : stack.erase.erase.activations ⊆ history) :
    ∃ answerPort : ScopedPorts.Port, ∃ table clauseFamilies declarationRequirements,
    SourceFocusHints.inputPort Instantiation.Environment.empty hint = some answerPort ∧
    ∀ activation answerType, activation ∉ history → ScopedPorts.eraseType answerType = answerPort →
    ∃ handler : SourceAnnotatedRuntime.Handler, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot world,
    ∃ actualPlans : SourceDeclarationPlans.ClausePlans handler.clauses.erase clauseFamilies,
      handler.activation = activation ∧ handler.answer = answerType ∧
      handler.clauses = clauses ∧ handler.scope = scope ∧ Instantiation.freezeEffect handler.effectInst = requested ∧
      RawStep ⟨.handle requested code.erase clauses.erase, scope, stack.erase⟩
        ⟨code.erase, scope, .push (.handler handler.erase) stack.erase⟩ [] [] ∧
      SourceAnnotatedRuntimeState.AtPlan operations policy contracts (RecursiveHandlerTables.register tables handler.activation table)
        (register families handler.activation clauseFamilies) (register required handler.activation declarationRequirements)
        actions annotations world outward outside scope code (.push (.handler handler) stack) nextSnapshot.plan nextSnapshot.forest output demand row evidence ∧
      SourceBoundSnapshots.EnteredHandler handler.effectInst table declarationRequirements actualPlans snapshot nextSnapshot ∧
      (∃ answer residual, answer.erase.erase.port = ScopedPorts.eraseType handler.answer ∧
        SourceAnnotatedSources.Declarations operations policy contracts world (fun _ => none) residual
          handler.effectInst answer handler.clauses table actualPlans) := by
  rcases snapshot with ⟨dependencies, plan, bounds, receiving, hints, forest, queued⟩
  cases state with
  | checked current scopeTyped pending closing templates matched contextual unique checked accepted accounting =>
    rename_i allowed answer bodyDemand currentRequirements ticket tailDemand tailRequirements resumes disposals
    generalize signatureSame : signature plan = currentSignature at current
    cases current with
    | checked hintCheck metadata node => cases node with
      | handler bodySource clausesTyped capabilities coverage clauseUnique admitted table modes declarations =>
        cases plan with
        | handler declarationRequirements plans bodyPlan =>
          obtain ⟨rfl, clausesSame, bodySame⟩ := SourcePlanSignatures.Signature.handler.inj signatureSame
          rw [← bodySame] at bodySource
          cases contextual with
          | handler recipes certified supplied bodyCheck =>
            obtain ⟨bodyRow, tailRow, currentCheck, tailCheck, sameRow⟩ :=
              RecursiveRequirements.checked_sequence_parts checked
            have checkedBody := RecursiveRequirements.checked_prepend_iff.mp
              (RecursiveRequirements.checked_prepend_iff.mp currentCheck)
            simp only [List.append_nil, List.cons_append, List.nil_append] at checkedBody
            rename_i sourceFamilies effect residual bodyDep bodySignature sourcePlans bodyRequirements planClauses
            refine ⟨answer.erase.erase.port, table, sourceFamilies, declarationRequirements,
              SourceFocusHints.check_source_iff.mp hintCheck, ?_⟩
            intro activation answerType fresh answerSame
            let handler : SourceAnnotatedRuntime.Handler := ⟨activation, effect, clauses, scope, answerType,
              ScopedPorts.clauses_have_ticket_barrier clausesTyped⟩
            let nextTables := RecursiveHandlerTables.register tables activation table
            let nextFamilies := register families activation sourceFamilies
            let nextRequired := register required activation declarationRequirements
            have freshStack : activation ∉ stack.erase.erase.activations := fun member => fresh (retained member)
            have tablesAgree : ∀ actual, actual.activation ∈ stack.erase.erase.activations → tables actual = nextTables actual :=
              RecursiveHandlerTables.register_agrees freshStack
            have familiesAgree : ∀ actual, actual.activation ∈ stack.erase.erase.activations → families actual = nextFamilies actual :=
              register_agrees freshStack
            have requiredAgree : ∀ actual, actual.activation ∈ stack.erase.erase.activations → required actual = nextRequired actual :=
              register_agrees freshStack
            have sameContext := context_congr tablesAgree
            have frame : SourceAnnotatedRuntimeTyping.Frame (evidence := evidence) operations policy contracts nextTables nextFamilies nextRequired outward actions
                (OwnerPhaseTransitions.available (ownedTickets stack.erase)) world (forest.append .nil)
                (.handler handler) answer answer [] (.request [] [])
                (.handler effect table sourceFamilies) (fun rest => .handler declarationRequirements rest) (fun rest => .handler rest)
                (effect :: residual) residual := by
              have base : SourceAnnotatedRuntimeTyping.Frame (evidence := evidence) operations policy contracts (fun _ => table) (fun _ => sourceFamilies)
                  (fun _ => declarationRequirements) outward actions (OwnerPhaseTransitions.available (ownedTickets stack.erase)) world
                  (forest.append .nil) (.handler handler) answer answer [] (.request [] [])
                  (.handler effect table sourceFamilies) (fun rest => .handler declarationRequirements rest) (fun rest => .handler rest)
                  (effect :: residual) residual :=
                (SourceStructuralHandlerEntry.handler_frame (handler := handler)
                  (tables := fun _ => table) (families := fun _ => sourceFamilies)
                  (required := fun _ => declarationRequirements)
                  (.handler recipes certified supplied bodyCheck) clausesSame
                  ⟨_, scopeTyped⟩ (by simp only [handler, answerSame])
                  clausesTyped coverage clauseUnique declarations capabilities modes).1
              apply base.registries_congr
              all_goals intro actual member
              all_goals change actual.activation ∈ [activation] at member
              all_goals have same := List.mem_singleton.mp member
              all_goals simp only [nextTables, nextFamilies, nextRequired, RecursiveHandlerTables.register, register, same, if_true]
            have pendingAfter := SourceAnnotatedRuntimeTyping.Segment.push frame
              ((pending.registries_congr tablesAgree familiesAgree requiredAgree).input_weaken admitted) (List.Subset.refl _)
            have active : Checked (resumes ++ disposals) (OwnerPhases.ofStack nextTables (.push (.handler handler.erase) stack.erase))
                (OwnerPhaseTransitions.available (ownedTickets stack.erase)) bodyRequirements bodyRow := by
              have relocated := checked_activation checkedBody (front := []) (tail := OwnerPhases.ofStack tables stack.erase)
                (second := activation) rfl
              simpa only [List.nil_append, OwnerPhases.ofStack, OwnerPhases.frameEntry, handler, SourceAnnotatedRuntime.Handler.erase, nextTables, RecursiveHandlerTables.register, if_true, sameContext]
                using relocated
            have afterBody : Checked (resumes ++ disposals) []
                (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets stack.erase)) bodyDemand)
                (.sequence ((Requirements.request [] []).prepend (OwnerPhases.ofStack nextTables stack.erase)) tailRequirements) tailRow :=
              .sequence (firstRow := []) (secondRow := tailRow)
                (.request (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])) tailCheck
            have prefixed := RecursiveRequirements.checked_prepend_iff.mpr
              (show Checked (resumes ++ disposals) (OwnerPhases.ofStack nextTables (.push (.handler handler.erase) stack.erase) ++ [])
                (OwnerPhaseTransitions.available (ownedTickets stack.erase)) bodyRequirements bodyRow from by
                  simpa only [List.append_nil] using active)
            have templatesAfter := (templates.tables_congr (nextTables := nextTables)).transport (nextRoot := .push (.handler handler) stack)
              (fun _ _ known => known) (fun _ _ known => known) (fun _ _ located => .push located)
            refine ⟨handler, ⟨_, bodyPlan, bounds.handlerBody, _, _,
              .handler (effect := effect) (table := table) (families := sourceFamilies) (required := declarationRequirements) forest,
              .handler queued⟩, sourcePlans, rfl, rfl, rfl, rfl, rfl,
              .enterHandler handler.erase code.erase stack.erase, ?_, .step bounds queued clausesSame, ⟨answer, residual, answerSame.symm, declarations⟩⟩
            rw [sameRow]
            exact .checked bodySource scopeTyped pendingAfter (.push (DeclaredSourceClosing.records_congr closing))
              templatesAfter (.handler matched) bodyCheck unique (.sequence prefixed afterBody) (sameRow ▸ accepted)
              (by simpa only [List.nil_append] using accounting)

theorem handler_annotations_exact
    (state : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      scope (.handle hint requested code clauses) stack forest output demand row evidence)
    (retained : stack.erase.erase.activations ⊆ history) :
    ∃ answerPort : ScopedPorts.Port, ∃ table clauseFamilies declarationRequirements,
    SourceFocusHints.inputPort Instantiation.Environment.empty hint = some answerPort ∧
    ∀ activation answerType, activation ∉ history → ScopedPorts.eraseType answerType = answerPort →
    ∃ handler : SourceAnnotatedRuntime.Handler, ∃ nextForest : SourceScheduledSavedPlans.Saved,
      handler.activation = activation ∧ handler.answer = answerType ∧
      handler.clauses = clauses ∧ handler.scope = scope ∧ Instantiation.freezeEffect handler.effectInst = requested ∧
      RawStep ⟨.handle requested code.erase clauses.erase, scope, stack.erase⟩
        ⟨code.erase, scope, .push (.handler handler.erase) stack.erase⟩ [] [] ∧
      SourceAnnotatedRuntimeState.State operations policy contracts (RecursiveHandlerTables.register tables handler.activation table)
        (register families handler.activation clauseFamilies) (register required handler.activation declarationRequirements)
        actions annotations world outward outside scope code (.push (.handler handler) stack) nextForest.forest output demand row evidence := by
  obtain ⟨dependencies, plan, indexed⟩ := state.atPlan
  let snapshot : SourceBoundSnapshots.Snapshot world :=
    ⟨_, plan, .absent, _, _, forest, .absent forest⟩
  obtain ⟨answerPort, table, clauseFamilies, declarationRequirements, portKnown, admitted⟩ :=
    handler_annotations_exact_snapshot snapshot indexed retained
  refine ⟨answerPort, table, clauseFamilies, declarationRequirements, portKnown, ?_⟩
  intro activation answerType fresh answerSame
  obtain ⟨handler, nextSnapshot, actualPlans, activationSame, typeSame, clausesSame, scopeSame, effectSame, raw, next, _, _⟩ :=
    admitted activation answerType fresh answerSame
  exact ⟨handler, ⟨_, _, nextSnapshot.forest⟩, activationSame, typeSame, clausesSame, scopeSame, effectSame, raw, next.state⟩

theorem handler_annotations
    (state : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      scope (.handle hint requested code clauses) stack forest output demand row evidence)
    (retained : stack.erase.erase.activations ⊆ history) :
    ∃ answerPort : ScopedPorts.Port, ∃ table clauseFamilies declarationRequirements,
    ∀ activation answerType, activation ∉ history → ScopedPorts.eraseType answerType = answerPort →
    ∃ handler : SourceAnnotatedRuntime.Handler, ∃ nextForest : SourceScheduledSavedPlans.Saved,
      handler.activation = activation ∧ handler.answer = answerType ∧
      RawStep ⟨.handle requested code.erase clauses.erase, scope, stack.erase⟩
        ⟨code.erase, scope, .push (.handler handler.erase) stack.erase⟩ [] [] ∧
      SourceAnnotatedRuntimeState.State operations policy contracts (RecursiveHandlerTables.register tables handler.activation table)
        (register families handler.activation clauseFamilies) (register required handler.activation declarationRequirements)
        actions annotations world outward outside scope code (.push (.handler handler) stack) nextForest.forest output demand row evidence := by
  obtain ⟨answerPort, table, clauseFamilies, declarationRequirements, portKnown, admitted⟩ :=
    handler_annotations_exact state retained
  refine ⟨answerPort, table, clauseFamilies, declarationRequirements, ?_⟩
  intro activation answerType fresh answerSame
  obtain ⟨handler, saved, activationSame, typeSame, clausesSame, scopeSame, effectSame, raw, next⟩ :=
    admitted activation answerType fresh answerSame
  exact ⟨handler, saved, activationSame, typeSame, raw, next⟩


theorem handler_preserves
    (state : SourceAnnotatedRuntimeState.State operations policy contracts tables families required actions annotations world outward outside
      scope (.handle hint requested code clauses) stack forest output demand row evidence)
    (retained : stack.erase.erase.activations ⊆ history) :
    ∃ handler : SourceAnnotatedRuntime.Handler, ∃ table clauseFamilies declarationRequirements, ∃ nextForest : SourceScheduledSavedPlans.Saved,
      handler.activation ∉ history ∧
      RawStep ⟨.handle requested code.erase clauses.erase, scope, stack.erase⟩
        ⟨code.erase, scope, .push (.handler handler.erase) stack.erase⟩ [] [] ∧
      SourceAnnotatedRuntimeState.State operations policy contracts (RecursiveHandlerTables.register tables handler.activation table)
        (register families handler.activation clauseFamilies) (register required handler.activation declarationRequirements)
        actions annotations world outward outside scope code (.push (.handler handler) stack) nextForest.forest output demand row evidence := by
  obtain ⟨answerPort, table, clauseFamilies, declarationRequirements, admitted⟩ := handler_annotations state retained
  obtain ⟨activation, fresh⟩ := ScopedTyping.fresh_world_name history
  obtain ⟨handler, saved, activationSame, _, raw, next⟩ :=
    admitted activation (ScopedPorts.embedPort answerPort) fresh (by simp)
  exact ⟨handler, table, clauseFamilies, declarationRequirements, saved, activationSame ▸ fresh, raw, next⟩

end Ash.OneShot.SourceAnnotatedRuntimeHandlers

#print axioms Ash.OneShot.SourceAnnotatedRuntimeTyping.Frame.registries_congr
#print axioms Ash.OneShot.SourceAnnotatedRuntimeTyping.Segment.registries_congr
#print axioms Ash.OneShot.SourceAnnotatedRuntimeTyping.Segment.input_weaken
#print axioms Ash.OneShot.SourceAnnotatedRuntimeHandlers.handler_annotations
#print axioms Ash.OneShot.SourceAnnotatedRuntimeHandlers.handler_preserves

#print axioms Ash.OneShot.SourceAnnotatedRuntimeHandlers.handler_annotations_exact

#print axioms Ash.OneShot.SourceAnnotatedRuntimeHandlers.handler_annotations_exact_snapshot
