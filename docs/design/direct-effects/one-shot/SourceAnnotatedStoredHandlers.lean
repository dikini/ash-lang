import SourceAnnotatedStoredState

/-! Handler entry installs the source-derived packet inside the joint runtime
invariant. The original typed frame, source checks and requirement accounting
are reused; the actual clause plan and its rich interfaces are shared. -/
namespace Ash.OneShot.SourceAnnotatedStoredHandlers
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
    (state : SourceAnnotatedRuntimeState.AtPackets operations policy contracts tables families required actions annotations world outward outside
      scope (.handle hint requested code clauses) stack snapshot.plan snapshot.forest output demand row stored evidence)
    (retained : stack.erase.erase.activations ⊆ history) :
    ∃ answerPort : ScopedPorts.Port, ∃ table clauseFamilies declarationRequirements,
    SourceFocusHints.inputPort Instantiation.Environment.empty hint = some answerPort ∧
    ∀ activation answerType, activation ∉ history → ScopedPorts.eraseType answerType = answerPort →
    ∃ handler : SourceAnnotatedRuntime.Handler, ∃ nextSnapshot : SourceBoundSnapshots.Snapshot world,
    ∃ actualPlans : SourceDeclarationPlans.ClausePlans handler.clauses.erase clauseFamilies,
    ∃ packet : SourceConsumingStoredBounds.HandlerBounds (register families handler.activation clauseFamilies) handler,
    ∃ nextStored : SourceConsumingStoredBounds.StackBounds (register families handler.activation clauseFamilies)
      (.push (.handler handler) stack),
      handler.activation = activation ∧ handler.answer = answerType ∧
      handler.clauses = clauses ∧ handler.scope = scope ∧ Instantiation.freezeEffect handler.effectInst = requested ∧
      RawStep ⟨.handle requested code.erase clauses.erase, scope, stack.erase⟩
        ⟨code.erase, scope, .push (.handler handler.erase) stack.erase⟩ [] [] ∧
      SourceAnnotatedRuntimeState.AtPackets operations policy contracts (RecursiveHandlerTables.register tables handler.activation table)
        (register families handler.activation clauseFamilies) (register required handler.activation declarationRequirements)
        actions annotations world outward outside scope code (.push (.handler handler) stack) nextSnapshot.plan nextSnapshot.forest output demand row nextStored evidence ∧
      SourceBoundSnapshots.EnteredHandler handler.effectInst table declarationRequirements actualPlans snapshot nextSnapshot ∧
      SourceBoundSnapshots.HandlerPacketFrom handler table declarationRequirements actualPlans snapshot packet ∧
      (∃ freshStack : handler.activation ∉ stack.erase.erase.activations,
        nextStored = .push (.handler packet) (stored.registries_congr (register_agrees freshStack))) := by
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
            let packet := bounds.handlerPacket (families := families) handler sourcePlans
            let nextStored : SourceConsumingStoredBounds.StackBounds nextFamilies (.push (.handler handler) stack) :=
              .push (.handler packet) (stored.registries_congr familiesAgree)
            have packetSource : SourceAnnotatedStoredTyping.PacketSource operations policy contracts nextTables nextFamilies nextRequired world evidence
                (.handler packet) answer answer (effect :: residual) residual := by
              refine .handler ?_ ?_
              · simpa only [packet, nextTables, RecursiveHandlerTables.register, handler, SourceAnnotatedRuntime.Handler.erase, if_true]
                  using bounds.handlerPacket_source (families := families) handler sourcePlans declarations
              · have retainedEvidence : evidence declarationRequirements sourcePlans :=
                  SourceStructuralHandlerEntry.DeclarationRetention.retain recipes clausesSame
                simpa only [packet, nextFamilies, nextRequired, register, handler, SourceAnnotatedRuntime.Handler.erase, if_true]
                  using bounds.handlerPacket_evidence (families := families) handler sourcePlans retainedEvidence
            have joinedFrame := SourceAnnotatedStoredTyping.Frame.mk frame packetSource
            have pendingAfter := SourceAnnotatedStoredTyping.Segment.push joinedFrame
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
              .handler queued⟩, sourcePlans, packet, nextStored, rfl, rfl, rfl, rfl, rfl,
              .enterHandler handler.erase code.erase stack.erase, ?_, .step bounds queued clausesSame,
              SourceBoundSnapshots.HandlerPacketFrom.step (handler := handler) (actual := sourcePlans) bounds queued clausesSame, ⟨freshStack, rfl⟩⟩
            rw [sameRow]
            exact .checked bodySource scopeTyped pendingAfter (.push (DeclaredSourceClosing.records_congr closing))
              templatesAfter (.handler matched) bodyCheck unique (.sequence prefixed afterBody) (sameRow ▸ accepted)
              (by simpa only [List.nil_append] using accounting)


end Ash.OneShot.SourceAnnotatedStoredHandlers

#print axioms Ash.OneShot.SourceAnnotatedStoredHandlers.handler_annotations_exact_snapshot
