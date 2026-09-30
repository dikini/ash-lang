import OwnerCaptureContracts

/-!
Closing-plan source evidence for the one-shot kernel. Executable release,
callback and retirement entries determine the source segment and its owner
transition. Callback effects are interpreted at the actual remaining plan and
receiving suffix; source handlers abandoned by disposal are not retained.
-/

namespace Ash.OneShot.OwnerClosingSource
open ScopedExpressions ScopedExecution CallableProtection ProtectionContracts ProtectionResiduals
open OwnerPhaseTransitions (Phases Trace spend project)
open OwnerSource

def retirements : List CloseEntry → List Nat
  | [] => []
  | .release _ _ :: rest | .invoke _ :: rest => retirements rest
  | .retire owner :: rest => owner :: retirements rest

theorem retirements_actual (scope : Scope) (plan : List CloseEntry) :
    retirements plan = ownedTickets (closeControl scope plan) := by
  induction plan with
  | nil => rfl
  | cons entry rest ih => cases entry <;> simp [retirements, closeControl, CloseEntry.frame, ownedTickets, ih]

theorem retirements_capture (built : makePlan capture = some plan) :
    (retirements plan).Perm (ownedTickets capture) := by
  rw [retirements_actual Execution.Scope.none]
  exact make_plan_preserves_owned_tickets built

theorem owned_names_subset (stack : Stack) : ownedTickets stack ⊆ stack.erase.ticketNames := by
  induction stack with
  | nil => simp [ownedTickets]
  | push frame rest ih => cases frame with
      | retiring ticket =>
          intro other member
          rcases List.mem_cons.mp member with same | present
          · simp [Stack.erase, ExecFrame.erase, CloseItem.frame, Control.ticketNames, same]
          · exact List.mem_cons_of_mem ticket (ih present)
      | plain | handler | cell | armed | running | unwinding | closing =>
          simpa [ownedTickets, Stack.erase, ExecFrame.erase, PlainData.erase, HandlerData.erase,
            ActionData.erase, CloseItem.frame, closeFrame, Control.ticketNames] using ih
  | live owner input answer saved caller rest ihSaved ihRest =>
      intro other member
      simp only [ownedTickets, List.mem_cons, List.mem_append] at member
      rcases member with same | savedMember | restMember
      · simp [Stack.erase, Control.ticketNames, same]
      · exact List.mem_cons_of_mem owner (List.mem_append_left _ (ihSaved savedMember))
      · exact List.mem_cons_of_mem owner (List.mem_append_right _ (ihRest restMember))
  | spent owner answer caller rest ih =>
      intro other member
      exact List.mem_cons_of_mem owner (ih member)

theorem plan_project (tables : CallableProtectionFrames.Tables) (scope : Scope) (plan : List CloseEntry) (phases : Phases) :
    project (OwnerPhases.ofStack tables (closeControl scope plan)) phases = DisposalProtection.planContext plan := by
  induction plan with
  | nil => rfl
  | cons entry rest ih => cases entry <;>
      simp [closeControl, CloseEntry.frame, OwnerPhases.ofStack, OwnerPhases.frameEntry,
        project, ExecFrame.erase, ActionData.erase, CloseItem.frame, ProtectionContexts.frameProtected, DisposalProtection.planContext, ih]

/-- Internal retirements cannot alter the receiving suffix's owner barriers
    when those owner names are absent from that suffix. -/
theorem suffix_spend (absent : owner ∉ OwnerPhases.names (OwnerPhases.ofStack tables fixed)) :
    exportAt (OwnerPhases.ofStack tables fixed) (spend before owner) raw =
      exportAt (OwnerPhases.ofStack tables fixed) before raw := by
  unfold exportAt
  rw [OwnerPhaseTransitions.project_spend_absent absent]

theorem callback_export
    (exported : exportAt (OwnerPhases.ofStack tables fixed) phases
      (DisposalProtection.callbackResidual rest latent) = some row) :
    exportAt (OwnerPhases.ofStack tables ((closeControl scope rest).append fixed)) phases (qualify true latent) = some row := by
  simp only [exportAt, OwnerPhases.stack_append, OwnerPhaseTransitions.project_append, plan_project]
  rw [residual_append, DisposalProtection.protected_row_residual]
  exact exported

/-- Existing callback source rows and the actual retirement sequence derive
    the complete planned source segment. Its result is unit-shaped, regardless
    of the answer type of the abandoned saved computation. -/
theorem plan_source
    (rows : DisposalProtection.Rows operations plan raw)
    (transition : Trace before (retirements plan) after)
    (separate : ∀ owner ∈ retirements plan, owner ∉ OwnerPhases.names (OwnerPhases.ofStack tables fixed))
    (exported : exportAt (OwnerPhases.ofStack tables fixed) before raw = some row) :
    Segment operations policy contracts tables fixed (closeControl scope plan) before .scalar after .scalar (retirements plan) row := by
  induction rows generalizing before after row with
  | nil =>
      cases transition
      simp only [exportAt, residual_empty] at exported
      cases exported
      exact .nil
  | release rest ih => exact .push .cell (ih transition separate exported)
  | retire rest ih =>
      cases transition with
      | cons ready remaining =>
          have tailSeparate := fun owner member => separate owner (List.mem_cons_of_mem _ member)
          have moved := (suffix_spend (separate _ List.mem_cons_self)).trans exported
          exact .push (.retiring (.cons ready .nil)) (ih remaining tailSeparate moved)
  | invoke callback rest ih =>
      rename_i environment latent plan raw action
      obtain ⟨callbackRow, restRow, callbackExport, restExport, same⟩ := split_export exported
      rw [same]
      exact .push (.armed (action := { action with scope := scope, answer := .unit }) callback
        (callback_export callbackExport)) (ih transition separate restExport)

/-- The executable plan, checked callback source and abandoned-use check are
    retained together. The exported row is computed at the receiving suffix. -/
structure ClosingData (operations : Operations) (capture : Stack) (plan : List CloseEntry) where
  rawRow : Footprint
  built : makePlan capture = some plan
  callbacks : DisposalProtection.Rows operations plan rawRow
  internal : InternalUses capture.erase.liveTickets capture.erase.pending

theorem closing_data
    (built : makePlan capture = some plan) (retained : DisposalProtection.Retained operations capture)
    (usage : OpenOwnerUses.Interface policy tickets capture outsideOwners)
    (separate : ∀ owner ∈ ownedTickets capture, owner ∉ outsideOwners)
    (empty : usage.external = []) : Nonempty (ClosingData operations capture plan) := by
  obtain ⟨row, callbacks⟩ := DisposalProtection.captured_disposal_row retained built
  exact ⟨⟨row, built, callbacks, OpenOwnerUses.external_empty_internal usage.source separate empty⟩⟩

def withClosing (contract : ResumeContract) (plan : List CloseEntry) (row : Footprint) : ResumeContract :=
  { contract with closeDemand := retirements plan, closeRow := some row }

theorem closing_unprotected (data : ClosingData operations capture plan) :
    ProtectionContexts.protectedMode capture.erase = false := by
  have possible := CaptureInterfaces.plan_available capture
  rw [data.built] at possible
  simpa using possible.symm

theorem attached_unprotected
    (saved : OwnerCaptureContracts.SavedSource operations policy contracts tables fixed capture before after contract)
    (data : ClosingData operations capture plan) : (withClosing contract plan row).held = false :=
  saved.held.trans (closing_unprotected data)

theorem discard_source_parts
    (source : Source operations policy contracts tables fixed outside scope (.discard binder) segment before after output demand row)
    (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner) :
    ∃ middle closingRow remaining restRow,
      contract.closeRow = some closingRow ∧ Trace before (owner :: contract.closeDemand) middle ∧
      Segment operations policy contracts tables fixed segment middle .scalar after output remaining restRow ∧
      demand = owner :: (contract.closeDemand ++ remaining) ∧ row = closingRow ++ restRow ∧
      checkFootprint outside row = true := by
  cases source with
  | checked current pending accepted => cases current with
      | stable summary exported => cases summary
      | discard actual target allowed unprotected closable transition =>
          have ownerSame := Option.some.inj (target.symm.trans resolved)
          subst_vars
          have contractSame := Option.some.inj (actual.symm.trans known)
          subst_vars
          exact ⟨_, _, _, _, closable, transition, pending, rfl, rfl, accepted⟩

section Disposal
variable {front capture tail fixed : Stack}

/-- Planned effects and retirement demands, checked at their real suffix,
    reconstruct the source after disposal. This does not derive the separate
    runtime check that abandoned syntax has no outside ticket obligation. -/
theorem discard_source
    (source : Source operations policy contracts tables fixed outside scope (.discard binder)
      (front.append (.live owner inputType answerType capture caller tail)) before after output demand row)
    (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
    (built : makePlan capture = some plan) (rows : DisposalProtection.Rows operations plan raw)
    (names : contract.closeDemand = retirements plan) (closable : contract.closeRow = some bound)
    (exported : exportAt (OwnerPhases.ofStack tables
      ((Stack.push (.closing closeId scope) (front.append (.spent owner answerType caller tail))).append fixed))
      (spend before owner) raw = some actualRow)
    (covered : EffectBounds.Covers bound actualRow)
    (separate : ∀ nested ∈ retirements plan, nested ∉ OwnerPhases.names (OwnerPhases.ofStack tables
      ((Stack.push (.closing closeId scope) (front.append (.spent owner answerType caller tail))).append fixed))) :
    contract.closeDemand.Perm (ownedTickets capture) ∧
    ∃ remaining restRow,
      demand = owner :: (contract.closeDemand ++ remaining) ∧ row = bound ++ restRow ∧
      Source operations policy contracts tables fixed outside scope .unit
        ((closeControl scope plan).append (.push (.closing closeId scope) (front.append (.spent owner answerType caller tail))))
        (spend before owner) after output (contract.closeDemand ++ remaining) (actualRow ++ restRow) := by
  obtain ⟨middle, closingRow, remaining, restRow, advertised, transition, pending, allNames, effects, accepted⟩ :=
    discard_source_parts source known resolved
  have boundSame := Option.some.inj (advertised.symm.trans closable)
  subst closingRow
  have consumed := OwnerPhaseTransitions.trace_consumed transition List.mem_cons_self
  have changed := OwnerSourceResumption.pending_live_to_spent pending consumed
  have plannedTrace : Trace (spend before owner) (retirements plan) middle := by
    cases transition with
    | cons ready rest => simpa only [names] using rest
  have planned := plan_source (policy := policy) (contracts := contracts) (scope := scope) rows plannedTrace separate exported
  have closing := Segment.push (FrameSource.closing (identity := closeId) (scope := scope)) changed
  have composed := segment_append planned closing
  have acceptedActual := EffectBounds.check_covered (effects ▸ accepted)
    (EffectBounds.covers_append_bounds covered (EffectBounds.covers_refl restRow))
  have restored := Source.checked
    (Derives.stable (environment := CallableProtection.Environment.empty) (scope := scope) (row := []) Summarizes.unit
      (by simp [exportAt, residual_empty])) composed (by simpa only [List.nil_append] using acceptedActual)
  refine ⟨names.symm ▸ retirements_capture built, remaining, restRow, allNames, effects, ?_⟩
  simpa only [List.nil_append, names] using restored

/-- The captured plan supplies the closing fields used by source disposal.
    Its effects are checked at this step's actual receiving suffix, and its
    abandoned-use evidence is retained alongside the resulting source. -/
theorem discard_source_from_data
    (data : ClosingData operations capture plan)
    (source : Source operations policy contracts tables fixed outside scope (.discard binder)
      (front.append (.live owner inputType answerType capture caller tail)) before after output demand row)
    (known : contracts owner = some (withClosing contract plan closingRow))
    (resolved : scope.resolve binder = some owner)
    (exported : exportAt (OwnerPhases.ofStack tables
      ((Stack.push (.closing closeId scope) (front.append (.spent owner answerType caller tail))).append fixed))
      (spend before owner) data.rawRow = some closingRow)
    (separate : ∀ nested ∈ retirements plan, nested ∉ OwnerPhases.names (OwnerPhases.ofStack tables
      ((Stack.push (.closing closeId scope) (front.append (.spent owner answerType caller tail))).append fixed))) :
    InternalUses capture.erase.liveTickets capture.erase.pending ∧
    (retirements plan).Perm (ownedTickets capture) ∧
    ∃ remaining restRow,
      demand = owner :: (retirements plan ++ remaining) ∧ row = closingRow ++ restRow ∧
      Source operations policy contracts tables fixed outside scope .unit
        ((closeControl scope plan).append (.push (.closing closeId scope) (front.append (.spent owner answerType caller tail))))
        (spend before owner) after output (retirements plan ++ remaining) (closingRow ++ restRow) := by
  exact ⟨data.internal, discard_source source known resolved data.built data.callbacks rfl rfl exported
    (EffectBounds.covers_refl _) separate⟩

/-- Disposal replaces the captured owners by exactly their planned retirements
    and consumes the selected owner immediately. -/
theorem discard_owned_permutation (built : makePlan capture = some plan) :
    (ownedTickets (front.append (.live owner inputType answerType capture caller tail))).Perm
      (owner :: ownedTickets ((closeControl scope plan).append
        (.push (.closing closeId scope) (front.append (.spent owner answerType caller tail))))) := by
  have restored := OwnerPhaseTransitions.resume_owned_permutation (front := front) (capture := capture) (tail := tail)
    (owner := owner) (input := inputType) (answer := answerType) (caller := caller)
  have planned := (make_plan_preserves_owned_tickets (scope := scope) built).symm.append_right
    (ownedTickets (front.append (.spent owner answerType caller tail)))
  exact restored.trans (.cons owner (by simpa only [owned_tickets_append, ownedTickets] using planned))

theorem discard_phase_trace (built : makePlan capture = some plan)
    (unique : (ownedTickets (front.append (.live owner inputType answerType capture caller tail))).Nodup) :
    Trace (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) [owner]
      (OwnerPhaseTransitions.available (ownedTickets ((closeControl scope plan).append
        (.push (.closing closeId scope) (front.append (.spent owner answerType caller tail)))))) := by
  have ordered := discard_owned_permutation (front := front) (tail := tail) (owner := owner)
    (inputType := inputType) (answerType := answerType) (caller := caller) (scope := scope) (closeId := closeId) built
  have absent := (List.nodup_cons.mp (ordered.nodup unique)).1
  rw [OwnerPhaseTransitions.available_permutation ordered]
  apply Trace.cons (by simp [OwnerPhaseTransitions.available])
  rw [OwnerPhaseTransitions.spend_available_cons absent]
  exact .nil

theorem retirements_separate
    (unique : (front.append (.live owner inputType answerType capture caller tail)).erase.ticketNames.Nodup)
    (built : makePlan capture = some plan) :
    ∀ nested ∈ retirements plan, nested ∉ OwnerPhases.names (OwnerPhases.ofStack tables
      (.push (.closing closeId scope) (front.append (.spent owner answerType caller tail)))) := by
  have ordered : (front.erase.ticketNames ++ owner :: (capture.erase.ticketNames ++ tail.erase.ticketNames)).Nodup := by
    simpa [Stack.erase, Control.ticketNames] using unique
  obtain ⟨_, innerUnique, disjointFront⟩ := List.nodup_append.mp ordered
  obtain ⟨ownerAbsent, capturedTailUnique⟩ := List.nodup_cons.mp innerUnique
  have disjointTail := (List.nodup_append.mp capturedTailUnique).2.2
  intro nested scheduled remaining
  have captured := owned_names_subset capture ((retirements_capture built).mem_iff.mp scheduled)
  simp only [OwnerPhases.ofStack, OwnerPhases.frameEntry, OwnerPhases.stack_append,
    OwnerPhases.names_append, OwnerPhases.names, List.mem_append, List.mem_cons] at remaining
  rcases remaining with inFront | same | inTail
  · exact disjointFront nested (OwnerPhases.stack_names_subset tables front inFront) nested
      (List.mem_cons_of_mem owner (List.mem_append_left _ captured)) rfl
  · subst nested
    exact ownerAbsent (List.mem_append_left _ captured)
  · exact disjointTail nested captured nested (OwnerPhases.stack_names_subset tables tail inTail) rfl

/-- Source disposal, planned retirement and the full runtime invariant concern
    the same named transition. Name history supplies suffix separation. -/
theorem discard_joint
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.discard binder, scope, front.append (.live owner inputType answerType capture caller tail)⟩,
        issued, completed⟩, activations⟩ result outgoing callableBound)
    (runtimeKnown : registry.joint.effects owner = some effectContract)
    (source : Source operations policy contracts tables .nil outside scope (.discard binder)
      (front.append (.live owner inputType answerType capture caller tail))
      (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture caller tail))))
      finalPhase output demand row)
    (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
    (built : makePlan capture = some plan) (rows : DisposalProtection.Rows operations plan raw)
    (names : contract.closeDemand = retirements plan) (closable : contract.closeRow = some bound)
    (exported : exportAt (OwnerPhases.ofStack tables
      (.push (.closing closeId scope) (front.append (.spent owner answerType caller tail))))
      (spend (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) owner)
      raw = some actualRow)
    (covered : EffectBounds.Covers bound actualRow)
    (planTyped : ScopedPorts.PlanTyped (DeclarationResults.signature declarations) (ScopedTyping.resourceWorld issued)
      effectContract.closeEffects plan)
    (fresh : (issued ++ [Owner.close closeId]).Nodup)
    (checks : AccessChecks ⟨.discard binder, scope, front.append (.live owner inputType answerType capture caller tail)⟩ ambient) :
    let before : NamedState := ⟨⟨⟨.discard binder, scope,
      front.append (.live owner inputType answerType capture caller tail)⟩, issued, completed⟩, activations⟩
    let after : Configuration := ⟨.unit, scope, (closeControl scope plan).append
      (.push (.closing closeId scope) (front.append (.spent owner answerType caller tail)))⟩
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [.close closeId] [.ticket owner]) ∧
    CompletionJoint.Valid declarations policy registry ambient
      (ScopedPortJoint.advanceState before after [.close closeId] [.ticket owner]) result outgoing callableBound ∧
    Trace (OwnerPhaseTransitions.available (ownedTickets before.execution.configuration.stack)) [owner]
      (OwnerPhaseTransitions.available (ownedTickets after.stack)) ∧
    contract.closeDemand.Perm (ownedTickets capture) ∧
    ∃ remaining restRow,
      demand = owner :: (contract.closeDemand ++ remaining) ∧ row = bound ++ restRow ∧
      Source operations policy contracts tables .nil outside scope .unit after.stack
        (OwnerPhaseTransitions.available (ownedTickets after.stack)) finalPhase output
        (contract.closeDemand ++ remaining) (actualRow ++ restRow) := by
  have distinct := (history_gives_distinct_names valid.joint.names valid.joint.ledger).1
  obtain ⟨_, _, _, _, _, _, unique⟩ := valid.joint.usage
  have separate := retirements_separate (tables := tables) (closeId := closeId) (scope := scope) distinct built
  obtain ⟨owned, remaining, restRow, demands, effects, restored⟩ := discard_source source known resolved built rows names closable
    (by simpa only [OwnerSourceResumption.stack_append_empty] using exported) covered
    (by simpa only [OwnerSourceResumption.stack_append_empty] using separate)
  have transition := discard_phase_trace (scope := scope) (closeId := closeId) built unique
  have phases := OwnerPhaseTransitions.trace_result transition
  change OwnerPhaseTransitions.available (ownedTickets ((closeControl scope plan).append
    (.push (.closing closeId scope) (front.append (.spent owner answerType caller tail))))) =
      spend (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) owner at phases
  obtain ⟨step, preserved⟩ := CompletionJoint.discard_preserves valid runtimeKnown resolved built planTyped fresh checks
  exact ⟨step, preserved, transition, owned, remaining, restRow, demands, effects, phases.symm ▸ restored⟩

end Disposal

section Completion

theorem source_start_cleanup
    (source : Source operations policy contracts tables fixed outside scope value (.push (.armed action) tail)
      before after output demand row)
    (closed : ClosedValue value) :
    Source operations policy contracts tables fixed outside .none (.app action.action .unit)
      (.push (.running action value closed) tail) before after output demand row := by
  cases source with
  | checked current pending accepted =>
      obtain ⟨valueSource, same, noDemand, noRow⟩ := value_summary current closed.1
      subst_vars
      cases pending with
      | push head rest => cases head with
          | armed callback exported =>
              have invocation := Derives.stable (policy := policy) (contracts := contracts) (scope := Execution.Scope.none)
                (inside := OwnerPhases.ofStack tables ((Stack.push (.running action value closed) tail).append fixed))
                (Summarizes.app callback Summarizes.unit) (by
                  simpa only [Stack.append, OwnerPhases.ofStack, OwnerPhases.frameEntry,
                    ExecFrame.erase, ProtectionContexts.frameProtected, project, exportAt,
                    residualize, DisposalProtection.through_barrier, List.nil_append] using exported)
              have restored := Source.checked invocation (Segment.push (FrameSource.running valueSource) rest) accepted
              simpa only [List.nil_append] using restored

theorem source_finish_cleanup
    (source : Source operations policy contracts tables fixed outside scope .unit (.push (.running action value closed) tail)
      before after output demand row) :
    Source operations policy contracts tables fixed outside action.scope value tail before after output demand row := by
  cases source with
  | checked current pending accepted =>
      obtain ⟨summary, same, noDemand, noRow⟩ := value_summary current trivial
      subst_vars
      cases pending with
      | push head rest => cases head with
          | running saved =>
              have restored := Source.checked
                (Derives.stable (scope := action.scope) (row := []) saved (by simp [exportAt, residual_empty])) rest accepted
              simpa only [List.nil_append] using restored

theorem source_finish_close
    (source : Source operations policy contracts tables fixed outside scope .unit (.push (.closing closeId caller) tail)
      before after output demand row) :
    Source operations policy contracts tables fixed outside caller .unit tail before after output demand row := by
  cases source with
  | checked current pending accepted =>
      obtain ⟨summary, same, noDemand, noRow⟩ := value_summary current trivial
      subst_vars
      cases pending with
      | push head rest => cases head with
          | closing =>
              have restored := Source.checked
                (Derives.stable (environment := CallableProtection.Environment.empty) (scope := caller) (row := []) Summarizes.unit
                  (by simp [exportAt, residual_empty])) rest accepted
              simpa only [List.nil_append] using restored

theorem source_retire
    (source : Source operations policy contracts tables fixed outside scope .unit (.push (.retiring owner) tail)
      before after output demand row) :
    ∃ remaining, demand = owner :: remaining ∧ before owner = .available ∧
      Source operations policy contracts tables fixed outside scope .unit tail
        (spend before owner) after output remaining row := by
  cases source with
  | checked current pending accepted =>
      obtain ⟨summary, same, noDemand, noRow⟩ := value_summary current trivial
      subst_vars
      cases pending with
      | push head rest => cases head with
          | retiring transition => cases transition with
              | cons ready endTrace =>
                  cases endTrace
                  rename_i environment phases remaining restRow
                  refine ⟨remaining, rfl, ready, ?_⟩
                  have restored := Source.checked
                    (Derives.stable (environment := CallableProtection.Environment.empty) (scope := scope) (row := []) Summarizes.unit
                      (by simp [exportAt, residual_empty])) rest accepted
                  simpa only [List.nil_append] using restored

theorem retired_owner_rejected
    (source : Source operations policy contracts tables fixed outside scope .unit (.push (.retiring owner) tail)
      before after output demand row)
    (consumed : before owner = .consumed) : False := by
  obtain ⟨remaining, names, ready, rest⟩ := source_retire source
  rw [consumed] at ready
  cases ready

theorem source_leave_cell
    (source : Source operations policy contracts tables fixed outside scope value (.push (.cell identity payload caller answerType) tail)
      before after output demand row)
    (isValue : value.IsValue) :
    Source operations policy contracts tables fixed outside caller value tail before after output demand row := by
  cases source with
  | checked current pending accepted =>
      obtain ⟨summary, same, noDemand, noRow⟩ := value_summary current isValue
      subst_vars
      cases pending with
      | push head rest => cases head with
          | cell =>
              have restored := Source.checked
                (Derives.stable (scope := caller) (row := []) summary (by simp [exportAt, residual_empty])) rest accepted
              simpa only [List.nil_append] using restored

end Completion

namespace Examples
open DisposalProtection.Examples (cellOperations cellAction cellRow cell_callback_summary nestedCapture nestedPlan nested_plan_derivation)
open OpenOwnerUses.Examples (policy tickets tables)

def waiting : PlainData := ⟨.bind 4 (.resume 10 .unit), .ticket 10 9, .unit, .unit, [9], rfl⟩
def capture : Stack := .push (.plain waiting) nestedCapture
def contract : ResumeContract := ⟨.scalar, .scalar, false, [9], [], [9], some []⟩
def contracts : Contracts := fun owner => if owner = 19 then some contract else if owner = 9 then some OwnerSource.Examples.neutral else none
def before : Configuration := ⟨.discard 20, .ticket 20 19, .live 19 .unit .unit capture .none .nil⟩
def after : Configuration := ⟨.unit, .ticket 20 19, (closeControl (.ticket 20 19) nestedPlan).append
  (.push (.closing 55 (.ticket 20 19)) (.spent 19 .unit .none .nil))⟩

theorem plan_built : makePlan capture = some nestedPlan := rfl

theorem callback_rows : DisposalProtection.Rows cellOperations nestedPlan [] := nested_plan_derivation.2.2

theorem plan_internal : InternalUses capture.erase.liveTickets capture.erase.pending :=
  .cons 9 [] (by decide) .nil

def closingData : ClosingData cellOperations capture nestedPlan := ⟨[], plan_built, callback_rows, plan_internal⟩

theorem before_source : Source cellOperations policy contracts tables .nil [] before.scope before.expression before.stack
    (OwnerPhaseTransitions.available (ownedTickets before.stack)) OwnerPhaseTransitions.empty .scalar [19, 9] [] := by
  have current : Derives cellOperations policy contracts (OwnerPhases.ofStack tables (before.stack.append .nil))
      CallableProtection.Environment.empty before.scope (OwnerPhaseTransitions.available (ownedTickets before.stack)) before.expression
      OwnerPhaseTransitions.empty .scalar [19, 9] [] :=
    .discard (contract := contract) rfl rfl rfl rfl rfl
      (OwnerPhaseTransitions.trace_all_owned (List.Perm.refl _) (by decide))
  exact .checked current (.live (contract := contract) rfl rfl rfl .nil) rfl

theorem after_source : Source cellOperations policy contracts tables .nil [] after.scope after.expression after.stack
    (OwnerPhaseTransitions.available (ownedTickets after.stack)) OwnerPhaseTransitions.empty .scalar [9] [] := by
  obtain ⟨internal, owned, remaining, restRow, names, effects, restored⟩ := discard_source_from_data (front := Stack.nil)
    (closeId := 55) closingData before_source (contract := contract) (closingRow := []) rfl rfl
    (by simp [closingData, exportAt, residual_empty])
    (by decide)
  have emptyDemand : remaining = [] := by simpa [nestedPlan, retirements] using names.symm
  have emptyRow : restRow = [] := effects.symm
  subst remaining
  subst restRow
  have phases := OwnerPhaseTransitions.trace_result (discard_phase_trace (front := Stack.nil) (tail := Stack.nil)
    (owner := 19) (inputType := Ty.unit) (answerType := Ty.unit) (caller := Execution.Scope.none)
    (scope := Execution.Scope.ticket 20 19) (closeId := 55) plan_built (by decide))
  change OwnerPhaseTransitions.available (ownedTickets after.stack) =
    spend (OwnerPhaseTransitions.available (ownedTickets before.stack)) 19 at phases
  rw [← phases] at restored
  exact restored

theorem captured_usage : StackUsage policy tickets capture [] [9] := by
  have saved : StackUsage policy tickets (.push (.armed cellAction) .nil) [] [] :=
    .push (.armed (action := cellAction) ⟨_, .none⟩ (ClauseProtection.stable_usage (cell_callback_summary (environment := .empty)) policy .none .available))
      (by simp [frameActiveDemand]) .nil
  have resource : StackUsage policy tickets (.push (.cell 42 17 .none .unit) .nil) [] [] :=
    .push (.cell ⟨_, .none⟩) (by simp [frameActiveDemand]) .nil
  have nested : StackUsage policy tickets nestedCapture [] [] := by
    exact .live (owner := 9) (captureDemand := []) rfl ⟨_, .none⟩
      (by simpa only [activeTickets, List.nil_append] using saved) resource
  exact .push (.plain (data := waiting) (.consume rfl (.bind .unit (.resume rfl .unit)))) (by decide) nested

theorem before_usage : ConfigurationUsage policy tickets before := by
  have pending : StackUsage policy tickets before.stack [] [9] := .live rfl ⟨_, .none⟩ captured_usage .nil
  exact ⟨[19], [9], .consume rfl (.discard rfl), pending, by decide, List.Perm.refl _, by decide⟩

theorem internal_obligations : InternalUses capture.erase.liveTickets capture.erase.pending := by
  exact plan_internal

theorem closing_data_generated : Nonempty (ClosingData cellOperations capture nestedPlan) :=
  closing_data plan_built ⟨trivial, nested_plan_derivation.1⟩ ⟨[9], captured_usage⟩ (by simp) rfl

theorem after_usage : ConfigurationUsage policy tickets after :=
  discard_preserves_configuration_usage (front := Stack.nil) before_usage rfl plan_built internal_obligations

theorem actual_discard : RawStep before after [.close 55] [.ticket 19] :=
  .discard 20 19 55 (.ticket 20 19) .none .unit .unit .nil capture .nil nestedPlan rfl plan_built

theorem immediate_and_pending_owners :
    OwnerPhaseTransitions.available (ownedTickets after.stack) 19 = .consumed ∧
    OwnerPhaseTransitions.available (ownedTickets after.stack) 9 = .available ∧ retirements nestedPlan = [9] := by decide

theorem callback_source : Source cellOperations policy contracts tables .nil [] .none (.app cellAction.action .unit)
    (.push (.running { cellAction with scope := .ticket 20 19, answer := .unit } .unit CallableProtection.Examples.unit_closed)
      ((closeControl (.ticket 20 19) [.retire 9, .release 42 17]).append
        (.push (.closing 55 (.ticket 20 19)) (.spent 19 .unit .none .nil))))
    (OwnerPhaseTransitions.available (ownedTickets after.stack)) OwnerPhaseTransitions.empty .scalar [9] [] :=
  source_start_cleanup after_source CallableProtection.Examples.unit_closed

theorem release_before_callback_rejected :
    checkFootprint [] (DisposalProtection.callbackResidual [] cellRow) = false := by decide

theorem disposal_evidence : RawStep before after [.close 55] [.ticket 19] ∧ ConfigurationUsage policy tickets after ∧
    Source cellOperations policy contracts tables .nil [] after.scope after.expression after.stack
      (OwnerPhaseTransitions.available (ownedTickets after.stack)) OwnerPhaseTransitions.empty .scalar [9] [] :=
  ⟨actual_discard, after_usage, after_source⟩

end Examples

end Ash.OneShot.OwnerClosingSource

#print axioms Ash.OneShot.OwnerClosingSource.retirements_actual
#print axioms Ash.OneShot.OwnerClosingSource.retirements_capture
#print axioms Ash.OneShot.OwnerClosingSource.owned_names_subset
#print axioms Ash.OneShot.OwnerClosingSource.plan_project
#print axioms Ash.OneShot.OwnerClosingSource.suffix_spend
#print axioms Ash.OneShot.OwnerClosingSource.callback_export
#print axioms Ash.OneShot.OwnerClosingSource.plan_source
#print axioms Ash.OneShot.OwnerClosingSource.closing_data
#print axioms Ash.OneShot.OwnerClosingSource.closing_unprotected
#print axioms Ash.OneShot.OwnerClosingSource.attached_unprotected
#print axioms Ash.OneShot.OwnerClosingSource.discard_source_parts
#print axioms Ash.OneShot.OwnerClosingSource.discard_source
#print axioms Ash.OneShot.OwnerClosingSource.discard_source_from_data
#print axioms Ash.OneShot.OwnerClosingSource.discard_owned_permutation
#print axioms Ash.OneShot.OwnerClosingSource.discard_phase_trace
#print axioms Ash.OneShot.OwnerClosingSource.retirements_separate
#print axioms Ash.OneShot.OwnerClosingSource.discard_joint
#print axioms Ash.OneShot.OwnerClosingSource.source_start_cleanup
#print axioms Ash.OneShot.OwnerClosingSource.source_finish_cleanup
#print axioms Ash.OneShot.OwnerClosingSource.source_finish_close
#print axioms Ash.OneShot.OwnerClosingSource.source_retire
#print axioms Ash.OneShot.OwnerClosingSource.retired_owner_rejected
#print axioms Ash.OneShot.OwnerClosingSource.source_leave_cell
#print axioms Ash.OneShot.OwnerClosingSource.Examples.plan_built
#print axioms Ash.OneShot.OwnerClosingSource.Examples.callback_rows
#print axioms Ash.OneShot.OwnerClosingSource.Examples.plan_internal
#print axioms Ash.OneShot.OwnerClosingSource.Examples.before_source
#print axioms Ash.OneShot.OwnerClosingSource.Examples.after_source
#print axioms Ash.OneShot.OwnerClosingSource.Examples.captured_usage
#print axioms Ash.OneShot.OwnerClosingSource.Examples.before_usage
#print axioms Ash.OneShot.OwnerClosingSource.Examples.internal_obligations
#print axioms Ash.OneShot.OwnerClosingSource.Examples.closing_data_generated
#print axioms Ash.OneShot.OwnerClosingSource.Examples.after_usage
#print axioms Ash.OneShot.OwnerClosingSource.Examples.actual_discard
#print axioms Ash.OneShot.OwnerClosingSource.Examples.immediate_and_pending_owners
#print axioms Ash.OneShot.OwnerClosingSource.Examples.callback_source
#print axioms Ash.OneShot.OwnerClosingSource.Examples.release_before_callback_rejected
#print axioms Ash.OneShot.OwnerClosingSource.Examples.disposal_evidence
