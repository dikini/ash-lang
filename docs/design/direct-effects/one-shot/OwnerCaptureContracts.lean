import OwnerSourceResumption

/-!
Source provenance for captured continuation contracts. The actual handler cut
determines the saved segment, full contracts, phase transition and effect row.
Registry extension retains those derivations. Closing-plan authentication and
transport to a changed resumption suffix remain separate obligations.
-/

namespace Ash.OneShot.OwnerCaptureContracts
open ScopedExpressions ScopedExecution CallableProtection ProtectionContracts ProtectionResiduals
open OwnerPhaseTransitions (Phases Trace spend project)
open OwnerSource

def Extends (before after : Contracts) : Prop :=
  ∀ owner contract, before owner = some contract → after owner = some contract

def insert (contracts : Contracts) (owner : Nat) (contract : ResumeContract) : Contracts :=
  fun other => if other = owner then some contract else contracts other

theorem insert_extends (fresh : contracts owner = none) : Extends contracts (insert contracts owner contract) := by
  intro other old known
  by_cases same : other = owner
  · subst other
    rw [fresh] at known
    cases known
  · simp only [insert, if_neg same, known]

theorem insert_lookup : insert contracts owner contract owner = some contract := by simp [insert]

theorem source_extension
    (source : Derives operations policy contracts inside environment scope before code after result demand row)
    (extension : Extends contracts larger) :
    Derives operations policy larger inside environment scope before code after result demand row := by
  induction source with
  | stable summary exported => exact .stable summary exported
  | pair left right ihLeft ihRight => exact .pair ihLeft ihRight
  | app function argument exported ihFunction ihArgument => exact .app ihFunction ihArgument exported
  | bind initializer body ihInit ihBody => exact .bind ihInit ihBody
  | branch condition yes no ihCondition ihYes ihNo => exact .branch ihCondition ihYes ihNo
  | perform known operand exported ih => exact .perform known ih exported
  | resume known resolved allowed operand transition ih => exact .resume (extension _ _ known) resolved allowed ih transition
  | discard known resolved allowed unprotected closable transition => exact .discard (extension _ _ known) resolved allowed unprotected closable transition
  | cleanup callback body exported ihCallback ihBody => exact .cleanup ihCallback ihBody exported
  | resource initializer body outward exported ih => exact .resource ih body outward exported

theorem context_extension
    (source : ContextDerives operations policy contracts inside environment scope position before input after output demand row)
    (extension : Extends contracts larger) :
    ContextDerives operations policy larger inside environment scope position before input after output demand row := by
  cases source with
  | pairLeft right => exact .pairLeft (source_extension right extension)
  | pairRight left => exact .pairRight left
  | appFunction argument exported => exact .appFunction (source_extension argument extension) exported
  | appArgument function exported => exact .appArgument function exported
  | bind body => exact .bind (source_extension body extension)
  | branch yes no => exact .branch (source_extension yes extension) (source_extension no extension)
  | perform known exported => exact .perform known exported
  | resume known resolved allowed transition => exact .resume (extension _ _ known) resolved allowed transition
  | cleanup body exported => exact .cleanup (source_extension body extension) exported
  | resource body outward exported => exact .resource body outward exported

theorem frame_extension
    (source : FrameSource operations policy contracts inside frame before input after output demand row)
    (extension : Extends contracts larger) :
    FrameSource operations policy larger inside frame before input after output demand row := by
  cases source with
  | plain source => exact .plain (context_extension source extension)
  | handler => exact .handler
  | cell => exact .cell
  | armed callback exported => exact .armed callback exported
  | running saved => exact .running saved
  | closing => exact .closing
  | retiring transition => exact .retiring transition

theorem segment_extension
    (source : Segment operations policy contracts tables fixed segment before input after output demand row)
    (extension : Extends contracts larger) :
    Segment operations policy larger tables fixed segment before input after output demand row := by
  induction source with
  | nil => exact .nil
  | push head tail ih => exact .push (frame_extension head extension) ih
  | live known held consumed tail ih => exact .live (extension _ _ known) held consumed ih
  | spent known consumed tail ih => exact .spent (extension _ _ known) consumed ih

theorem configuration_extension
    (source : Source operations policy contracts tables fixed outside scope code segment before after output demand row)
    (extension : Extends contracts larger) :
    Source operations policy larger tables fixed outside scope code segment before after output demand row := by
  cases source with
  | checked current pending accepted => exact .checked (source_extension current extension) (segment_extension pending extension) accepted

/-- Only the resume fields are authenticated here. Close fields are retained
    as annotations until a structural closing-plan derivation checks them. -/
structure SavedSource (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (fixed capture : Stack)
    (before after : Phases) (contract : ResumeContract) where
  actualRow : Footprint
  source : Segment operations policy contracts tables fixed capture before contract.input after contract.answer contract.resumeDemand actualRow
  covered : EffectBounds.Covers contract.resumeRow actualRow
  held : contract.held = ProtectionContexts.protectedMode capture.erase

def SavedSource.extend
    (saved : SavedSource operations policy contracts tables fixed capture before after contract)
    (extension : Extends contracts larger) : SavedSource operations policy larger tables fixed capture before after contract :=
  ⟨saved.actualRow, segment_extension saved.source extension, saved.covered, saved.held⟩

theorem saved_transition (saved : SavedSource operations policy contracts tables fixed capture before after contract) :
    Trace before contract.resumeDemand after := segment_trace saved.source

theorem saved_once (saved : SavedSource operations policy contracts tables fixed capture before after contract) :
    contract.resumeDemand.Nodup := segment_no_repeated_owner saved.source

theorem saved_endpoint (saved : SavedSource operations policy contracts tables fixed capture before after contract) :
    after = OwnerPhaseTransitions.spendAll before contract.resumeDemand :=
  OwnerPhaseTransitions.trace_result (saved_transition saved)

theorem extension_retains_saved (saved : SavedSource operations policy contracts tables fixed capture before after contract)
    (extension : Extends contracts larger) : (saved.extend extension).actualRow = saved.actualRow := rfl

theorem spend_introduced (consumed : before owner = .consumed) :
    spend (OwnerPhaseTransitions.introduce before owner) owner = before := by
  funext other
  by_cases same : other = owner <;> simp [spend, OwnerPhaseTransitions.introduce, same, consumed]

theorem saved_resume_transition
    (saved : SavedSource operations policy contracts tables fixed capture before after contract)
    (consumed : before owner = .consumed) :
    Trace (OwnerPhaseTransitions.introduce before owner) (owner :: contract.resumeDemand) after := by
  apply Trace.cons (by simp [OwnerPhaseTransitions.introduce])
  rw [spend_introduced consumed]
  exact saved_transition saved

/-- Rebase source evidence only when the actual ordered projections agree at
    the relevant consumed-owner phases. No handler exchange law is assumed. -/
def SavedSource.rebase
    (saved : SavedSource operations policy contracts tables fixed capture before after contract)
    (consumed : before owner = .consumed)
    (same : ∀ phases, phases owner = .consumed →
      project (OwnerPhases.ofStack tables fixed) phases = project (OwnerPhases.ofStack tables receiving) phases) :
    SavedSource operations policy contracts tables receiving capture before after contract :=
  ⟨saved.actualRow, OwnerSourceResumption.segment_fixed_spent saved.source consumed same, saved.covered, saved.held⟩

theorem saved_resume_segment
    (saved : SavedSource operations policy contracts tables fixed capture before after contract)
    (consumed : before owner = .consumed) :
    Segment operations policy contracts tables fixed capture
      (spend (OwnerPhaseTransitions.introduce before owner) owner) contract.input
      (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.introduce before owner) (owner :: contract.resumeDemand))
      contract.answer contract.resumeDemand saved.actualRow := by
  rw [spend_introduced consumed, ← OwnerPhaseTransitions.trace_result (saved_resume_transition saved consumed)]
  exact saved.source

section Capture
variable {whole capture tail fixed : Stack}
variable {contracts : Contracts} {registry larger : CallableJoint.Registry}

/-- The capture contract's resume fields are extracted from the actual source
    cut. Supplying close annotations does not authenticate those annotations. -/
theorem capture_contract
    (cut : HandlerCut requested whole capture tail handler)
    (source : Source operations policy contracts tables fixed outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole before after output demand row)
    (isValue : operand.IsValue) (closeDemand : List Nat) (closeRow : Option Footprint) :
    ∃ environment raw requestRow middle, ∃ contract : ResumeContract, ∃ remaining restRow,
      Summarizes operations environment (.perform (Instantiation.freezeEffect requested) operation operand) contract.input raw ∧
      exportAt (OwnerPhases.ofStack tables (whole.append fixed)) before raw = some requestRow ∧
      Nonempty (SavedSource operations policy contracts tables (tail.append fixed) capture before middle contract) ∧
      Segment operations policy contracts tables fixed tail middle contract.answer after output remaining restRow ∧
      contract.closeDemand = closeDemand ∧ contract.closeRow = closeRow ∧
      demand = contract.resumeDemand ++ remaining ∧ row = requestRow ++ (contract.resumeRow ++ restRow) ∧
      checkFootprint outside (contract.resumeRow ++ restRow) = true := by
  cases source with
  | checked current pending accepted =>
      obtain ⟨raw, summary, same, noDemand, exported⟩ := request_summary current isValue
      subst_vars
      obtain ⟨middle, answer, savedDemand, remaining, savedRow, restRow, saved, rest, names, effects⟩ :=
        capture_segment cut pending
      rename_i environment start input requestRow totalDemand totalRow
      let contract : ResumeContract := ⟨input, answer, ProtectionContexts.protectedMode capture.erase,
        savedDemand, savedRow, closeDemand, closeRow⟩
      refine ⟨_, raw, _, middle, contract, remaining, restRow, summary, exported,
        ⟨⟨savedRow, saved, EffectBounds.covers_refl _, rfl⟩⟩, rest, rfl, rfl, ?_, ?_, ?_⟩
      · simpa only [List.nil_append] using names
      · exact congrArg (_ ++ ·) effects
      · rw [check_footprint_append, Bool.and_eq_true_iff] at accepted
        simpa only [effects] using accepted.2

/-- Historical registration connects source-name freshness to the same runtime
    allocation. It does not assert agreement of their contract contents. -/
theorem source_registry_fresh
    (registered : ∀ name contract, contracts name = some contract → ∃ record, registry name = some record)
    (fresh : registry owner = none) : contracts owner = none := by
  cases found : contracts owner with
  | none => rfl
  | some contract =>
      obtain ⟨record, known⟩ := registered owner contract found
      rw [fresh] at known
      cases known

theorem registration_extension
    (registered : ∀ name contract, contracts name = some contract → ∃ record, registry name = some record)
    (extension : CallableJoint.RegistryExtends registry larger)
    (allocated : larger owner = some record) :
    ∀ name contract, insert contracts owner freshContract name = some contract → ∃ record, larger name = some record := by
  intro name contract known
  by_cases same : name = owner
  · subst name
    exact ⟨record, allocated⟩
  · simp only [insert, if_neg same] at known
    obtain ⟨old, oldKnown⟩ := registered name contract known
    exact ⟨old, extension _ _ oldKnown⟩

/-- Fresh capture installs the contract obtained from the source cut under the
    same owner as the runtime record. The retained source and raw usage concern
    the same saved stack; their demand lists are not assumed equal. -/
theorem capture_joint
    (cut : HandlerCut requested whole capture tail handler)
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ result outgoing bound)
    (source : Source operations policy contracts tables .nil outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole
      (OwnerPhaseTransitions.available (ownedTickets whole)) finalPhase output demand row)
    (registered : ∀ name contract, contracts name = some contract → ∃ record, registry name = some record)
    (isValue : operand.IsValue) (fresh : (issued ++ [Owner.ticket owner]).Nodup)
    (closeDemand : List Nat) (closeRow : Option Footprint) :
    ∃ (parameter binder : Nat) (body : Code) (port : ScopedPorts.Port) (record : CallableJoint.TicketRecord),
      ∃ contract : ResumeContract, ∃ middle,
      ClauseAt operation handler.clauses parameter binder body ∧
      let before : NamedState := ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩
      let after : Configuration := ⟨body.subst parameter operand, .ticket binder owner,
        .live owner (ScopedPorts.embedPort port) handler.answer capture handler.scope tail⟩
      NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [.ticket owner] []) ∧
      CompletionJoint.Valid declarations policy (registry.insert owner record) ambient
        (ScopedPortJoint.advanceState before after [.ticket owner] []) result outgoing bound ∧
      OwnerPhaseTransitions.available (ownedTickets after.stack) =
        OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner ∧
      Extends contracts (insert contracts owner contract) ∧
      insert contracts owner contract owner = some contract ∧
      (∀ name old, insert contracts owner contract name = some old → ∃ actual, (registry.insert owner record) name = some actual) ∧
      Nonempty (SavedSource operations policy (insert contracts owner contract) tables tail capture
        (OwnerPhaseTransitions.available (ownedTickets whole)) middle contract) ∧
      Nonempty (OpenOwnerUses.Interface policy (registry.insert owner record).joint.usage capture (activeTickets tail)) ∧
      contract.closeDemand = closeDemand ∧ contract.closeRow = closeRow ∧
      ∃ remaining restRow,
        Segment operations policy (insert contracts owner contract) tables .nil tail middle contract.answer finalPhase output remaining restRow ∧
        demand = contract.resumeDemand ++ remaining ∧ checkFootprint outside (contract.resumeRow ++ restRow) = true := by
  obtain ⟨environment, raw, requestRow, middle, contract, remaining, restRow, summary, exported, ⟨saved⟩,
    rest, closeNames, closeEffects, names, effects, accepted⟩ := capture_contract cut source isValue closeDemand closeRow
  have sourceFresh := source_registry_fresh registered (CompletionJoint.registry_fresh valid fresh)
  have sourceExtension := insert_extends (contract := contract) sourceFresh
  obtain ⟨parameter, binder, body, port, residual, record, recordEq, selected, signature,
    extension, step, preserved⟩ := CompletionJoint.capture_without_payload_premise cut valid isValue fresh
  have usageExtension := CapturedPhaseContracts.registry_usage_extension extension
  obtain ⟨interface, runtimeRemaining, runtimeMiddle, tailUsage, capturedTrace, remainingTrace, externalTrace⟩ :=
    OwnerPhaseTransitions.capture_trace valid.joint.usage cut isValue
  have retained := saved.extend sourceExtension
  refine ⟨parameter, binder, body, port, record, contract, middle, selected, step, preserved,
    OwnerPhaseTransitions.capture_map cut, sourceExtension, insert_lookup, ?_, ?_, ?_, closeNames, closeEffects,
    remaining, restRow, segment_extension rest sourceExtension, names, accepted⟩
  · exact registration_extension (record := record) (owner := owner) (freshContract := contract) registered extension
      (by simp [CallableJoint.Registry.insert])
  · exact ⟨by simpa only [OwnerSourceResumption.stack_append_empty] using retained⟩
  · exact ⟨⟨interface.demand, stack_usage_extension interface.source usageExtension⟩⟩

/-- Once the selected clause has a structural source derivation, closed payload
    substitution and the original surviving tail construct its after-source.
    This premise belongs in the handler's source rule, not in runtime progress. -/
theorem clause_source
    (saved : SavedSource operations policy contracts tables (tail.append fixed) capture before middle contract)
    (rest : Segment operations policy contracts tables fixed tail middle contract.answer after output remaining restRow)
    (fresh : contracts owner = none) (consumed : middle owner = .consumed)
    (clause : Derives operations policy (insert contracts owner contract)
      (OwnerPhases.ofStack tables ((Stack.live owner inputType answerType capture caller tail).append fixed))
      (environment.extend parameter payload) (.ticket binder owner)
      (OwnerPhaseTransitions.introduce before owner) body middle contract.answer clauseDemand clauseRow)
    (operand : Summarizes operations environment value payload []) (closed : ClosedValue value)
    (accepted : checkFootprint outside (clauseRow ++ restRow) = true) :
    Source operations policy (insert contracts owner contract) tables fixed outside (.ticket binder owner)
      (body.subst parameter value) (.live owner inputType answerType capture caller tail)
      (OwnerPhaseTransitions.introduce before owner) after output
      (clauseDemand ++ remaining) (clauseRow ++ restRow) := by
  exact .checked (substitution clause operand closed)
    (.live insert_lookup saved.held consumed (segment_extension rest (insert_extends fresh))) accepted

/-- Captured source provenance supplies the resumption premise after checked
    interpretation transport. The waiting stack may have any constructor. -/
theorem resume_from_saved_source {front : Stack}
    (saved : SavedSource operations policy contracts tables (tail.append fixed) capture before capturedAfter contract)
    (consumed : before owner = .consumed)
    (source : Source operations policy contracts tables fixed outside scope (.resume binder value)
      (front.append (.live owner inputType answerType capture caller tail))
      (OwnerPhaseTransitions.introduce before owner) after output demand row)
    (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner) (isValue : value.IsValue)
    (same : ∀ phases, phases owner = .consumed →
      project (OwnerPhases.ofStack tables (tail.append fixed)) phases =
        project (OwnerPhases.ofStack tables ((front.append (.spent owner answerType caller tail)).append fixed)) phases) :
    ∃ remaining restRow,
      demand = owner :: (contract.resumeDemand ++ remaining) ∧ row = contract.resumeRow ++ restRow ∧
      Source operations policy contracts tables fixed outside scope value
        (capture.append (front.append (.spent owner answerType caller tail)))
        before after output (contract.resumeDemand ++ remaining) (saved.actualRow ++ restRow) := by
  let moved := saved.rebase consumed same
  obtain ⟨remaining, restRow, names, effects, restored⟩ := OwnerSourceResumption.restored_source source known resolved isValue
    (saved_resume_segment moved consumed) moved.covered
  rw [spend_introduced consumed] at restored
  exact ⟨remaining, restRow, names, effects, restored⟩

theorem spent_suffix_agrees (phases : Phases) :
    project (OwnerPhases.ofStack tables (tail.append fixed)) phases =
      project (OwnerPhases.ofStack tables ((Stack.spent owner answer caller tail).append fixed)) phases := rfl

end Capture

namespace Examples
open OpenOwnerUses.Examples (operations policy tickets tables tail localHandler waiting handled request)
open OwnerPhaseTransitions.Examples (innerWaiting capture whole beforeResume afterResume)
open OwnerSource.Examples (neutral captured initial after29 consume29 consume9)

def prior : Contracts := fun owner => if owner = 29 ∨ owner = 9 then some neutral else none
def allocated : Contracts := insert prior 19 captured

theorem prior_fresh : prior 19 = none := rfl

theorem allocated_retains_prior : Extends prior allocated := insert_extends prior_fresh

theorem allocated_agrees : allocated = OwnerSource.Examples.contracts := by
  funext owner
  by_cases same : owner = 19 <;> simp [allocated, insert, prior, OwnerSource.Examples.contracts, same]

theorem unit_source (inside : OwnerPhases.Context) (environment : CallableProtection.Environment) (scope : Scope) (phases : Phases) :
    Derives operations policy prior inside environment scope phases .unit phases .scalar [] [] :=
  .stable .unit (by simp [exportAt, residual_empty])

theorem captured_source (fixed : Stack) : Segment operations policy prior tables fixed capture
    initial .scalar OwnerPhaseTransitions.empty .scalar [29, 9] [] := by
  have use29 (inside : OwnerPhases.Context) (environment : CallableProtection.Environment) :
      Derives operations policy prior inside environment (.ticket 30 29) initial (.resume 30 .unit) after29 .scalar [29] [] :=
    .resume (contract := neutral) rfl rfl rfl (unit_source _ _ _ _) consume29
  have use9 (inside : OwnerPhases.Context) (environment : CallableProtection.Environment) :
      Derives operations policy prior inside environment (.ticket 10 9) after29 (.resume 10 .unit)
        OwnerPhaseTransitions.empty .scalar [9] [] :=
    .resume (contract := neutral) rfl rfl rfl (unit_source _ _ _ _) consume9
  have outerHead : ContextDerives operations policy prior
      (OwnerPhases.ofStack tables ((Stack.push (.handler localHandler) .nil).append fixed))
      CallableProtection.Environment.empty waiting.scope waiting.context after29 .scalar OwnerPhaseTransitions.empty .scalar [9] [] :=
    .bind (use9 _ _)
  have rest : Segment operations policy prior tables fixed OpenOwnerUses.Examples.capture
      after29 .scalar OwnerPhaseTransitions.empty .scalar [9] [] := .push (.plain outerHead) (.push .handler .nil)
  have innerHead : ContextDerives operations policy prior
      (OwnerPhases.ofStack tables ((Stack.live 29 .unit .unit .nil (.ticket 10 9) OpenOwnerUses.Examples.capture).append fixed))
      CallableProtection.Environment.empty innerWaiting.scope innerWaiting.context initial .scalar after29 .scalar [29] [] :=
    .bind (use29 _ _)
  exact .push (.plain innerHead) (.live (contract := neutral) rfl rfl rfl rest)

theorem tail_source : Segment operations policy prior tables .nil tail
    OwnerPhaseTransitions.empty .scalar OwnerPhaseTransitions.empty .scalar [] [] :=
  .live (contract := neutral) rfl rfl rfl .nil

theorem request_source : Source operations policy prior tables .nil [] (.ticket 30 29) request whole
    initial OwnerPhaseTransitions.empty .scalar [29, 9] [] := by
  have pending := segment_append (front := capture) (firstDemand := [29, 9]) (firstRow := []) (captured_source tail) tail_source
  have current : Derives operations policy prior (OwnerPhases.ofStack tables (whole.append .nil))
      CallableProtection.Environment.empty (.ticket 30 29) initial request initial .scalar [] [] :=
    .perform (requestRow := []) rfl (unit_source _ _ _ _) (by decide)
  exact .checked current pending rfl

theorem cut_derives_resume_contract : ∃ contract : ResumeContract, ∃ middle remaining,
    Nonempty (SavedSource operations policy prior tables tail capture initial middle contract) ∧
    [29, 9] = contract.resumeDemand ++ remaining := by
  obtain ⟨environment, raw, requestRow, middle, contract, remaining, restRow, summary, exported, saved,
    rest, closeNames, closeEffects, names, effects, accepted⟩ :=
    capture_contract OwnerPhaseTransitions.Examples.selected_cut request_source trivial [29] none
  exact ⟨contract, middle, remaining, by simpa only [OwnerSourceResumption.stack_append_empty] using saved, names⟩

def saved : SavedSource operations policy prior tables tail capture initial OwnerPhaseTransitions.empty captured :=
  ⟨[], captured_source tail, EffectBounds.covers_refl [], rfl⟩

def retained : SavedSource operations policy allocated tables tail capture initial OwnerPhaseTransitions.empty captured :=
  saved.extend allocated_retains_prior

theorem introduced_map : OwnerPhaseTransitions.introduce initial 19 =
    OwnerPhaseTransitions.available (ownedTickets beforeResume.stack) :=
  (OwnerPhaseTransitions.capture_map (owner := 19) (input := Ty.unit) OwnerPhaseTransitions.Examples.selected_cut).symm

/-- The selected clause's source is checked with the freshly derived contract;
    the after-capture source is then constructed by the general source rule. -/
theorem after_capture_source : Source operations policy allocated tables .nil [] (.ticket 20 19) (.resume 20 .unit)
    beforeResume.stack (OwnerPhaseTransitions.available (ownedTickets beforeResume.stack))
    OwnerPhaseTransitions.empty .scalar [19, 29, 9] [] := by
  have clause : Derives operations policy allocated (OwnerPhases.ofStack tables (beforeResume.stack.append .nil))
      (CallableProtection.Environment.empty.extend 2 .scalar) (.ticket 20 19)
      (OwnerPhaseTransitions.introduce initial 19) (.resume 20 .unit) OwnerPhaseTransitions.empty .scalar [19, 29, 9] [] :=
    .resume (contract := captured) insert_lookup rfl rfl
      (.stable (row := []) .unit (by simp [exportAt, residual_empty])) (saved_resume_transition saved rfl)
  have result := clause_source (outside := []) (inputType := Ty.unit) (answerType := Ty.integer) (caller := Execution.Scope.ticket 10 9)
    (fixed := Stack.nil) (value := Code.unit) (by simpa only [OwnerSourceResumption.stack_append_empty] using saved)
    tail_source prior_fresh rfl clause Summarizes.unit CallableProtection.Examples.unit_closed rfl
  rw [introduced_map] at result
  exact result

theorem actual_capture : RawStep ⟨request, .ticket 30 29, whole⟩ beforeResume [.ticket 19] [] :=
  .capture handled 0 2 20 19 .unit (.resume 20 .unit) (.ticket 30 29) whole capture tail localHandler .unit
    OwnerPhaseTransitions.Examples.selected_cut .hit CallableProtection.Examples.unit_closed
      (by simp [ClosedExcept, Code.dependencies])

/-- The capture's retained source supplies the subsequent resumption proof;
    no independently supplied after-resume source is used. -/
theorem after_resume_source : Source operations policy allocated tables .nil [] (.ticket 20 19) .unit afterResume.stack
    initial OwnerPhaseTransitions.empty .scalar [29, 9] [] := by
  have before := after_capture_source
  rw [← introduced_map] at before
  obtain ⟨remaining, restRow, names, effects, restored⟩ := resume_from_saved_source
    (front := Stack.nil) (by simpa only [OwnerSourceResumption.stack_append_empty] using retained)
    rfl before insert_lookup rfl trivial (fun phases _ => spent_suffix_agrees phases)
  have emptyDemand : remaining = [] := by simpa [captured] using names.symm
  have emptyRow : restRow = [] := effects.symm
  subst remaining
  subst restRow
  exact restored

theorem capture_then_resume_evidence :
    RawStep ⟨request, .ticket 30 29, whole⟩ beforeResume [.ticket 19] [] ∧
    RawStep beforeResume afterResume [] [.ticket 19] ∧
    ConfigurationUsage policy tickets beforeResume ∧ ConfigurationUsage policy tickets afterResume ∧
    Source operations policy allocated tables .nil [] (.ticket 20 19) .unit afterResume.stack
      initial OwnerPhaseTransitions.empty .scalar [29, 9] [] :=
  ⟨actual_capture, OwnerPhaseTransitions.Examples.actual_resume, OwnerPhaseTransitions.Examples.before_resume_usage,
    OwnerPhaseTransitions.Examples.after_resume_usage, after_resume_source⟩

theorem duplicate_insertion_not_extension : ¬ Extends prior (insert prior 29 captured) := by
  intro extension
  have changed := extension 29 neutral rfl
  simp [insert, captured, neutral] at changed

/-- A newly installed waiting handler can change the exported row. The
    projection-agreement premise is not available for every waiting suffix. -/
theorem waiting_handler_changes_residual :
    exportAt (OwnerPhases.ofStack tables tail) OwnerPhaseTransitions.empty [⟨handled, 0, false⟩] ≠
      exportAt (OwnerPhases.ofStack tables
        (.push (.handler localHandler) (.spent 19 .integer (.ticket 10 9) tail)))
        OwnerPhaseTransitions.empty [⟨handled, 0, false⟩] := by decide

end Examples

end Ash.OneShot.OwnerCaptureContracts

#print axioms Ash.OneShot.OwnerCaptureContracts.insert_extends
#print axioms Ash.OneShot.OwnerCaptureContracts.insert_lookup
#print axioms Ash.OneShot.OwnerCaptureContracts.source_extension
#print axioms Ash.OneShot.OwnerCaptureContracts.context_extension
#print axioms Ash.OneShot.OwnerCaptureContracts.frame_extension
#print axioms Ash.OneShot.OwnerCaptureContracts.segment_extension
#print axioms Ash.OneShot.OwnerCaptureContracts.configuration_extension
#print axioms Ash.OneShot.OwnerCaptureContracts.saved_transition
#print axioms Ash.OneShot.OwnerCaptureContracts.saved_once
#print axioms Ash.OneShot.OwnerCaptureContracts.saved_endpoint
#print axioms Ash.OneShot.OwnerCaptureContracts.extension_retains_saved
#print axioms Ash.OneShot.OwnerCaptureContracts.spend_introduced
#print axioms Ash.OneShot.OwnerCaptureContracts.saved_resume_transition
#print axioms Ash.OneShot.OwnerCaptureContracts.saved_resume_segment
#print axioms Ash.OneShot.OwnerCaptureContracts.capture_contract
#print axioms Ash.OneShot.OwnerCaptureContracts.source_registry_fresh
#print axioms Ash.OneShot.OwnerCaptureContracts.registration_extension
#print axioms Ash.OneShot.OwnerCaptureContracts.capture_joint
#print axioms Ash.OneShot.OwnerCaptureContracts.clause_source
#print axioms Ash.OneShot.OwnerCaptureContracts.resume_from_saved_source
#print axioms Ash.OneShot.OwnerCaptureContracts.spent_suffix_agrees
#print axioms Ash.OneShot.OwnerCaptureContracts.Examples.prior_fresh
#print axioms Ash.OneShot.OwnerCaptureContracts.Examples.allocated_retains_prior
#print axioms Ash.OneShot.OwnerCaptureContracts.Examples.allocated_agrees
#print axioms Ash.OneShot.OwnerCaptureContracts.Examples.unit_source
#print axioms Ash.OneShot.OwnerCaptureContracts.Examples.captured_source
#print axioms Ash.OneShot.OwnerCaptureContracts.Examples.tail_source
#print axioms Ash.OneShot.OwnerCaptureContracts.Examples.request_source
#print axioms Ash.OneShot.OwnerCaptureContracts.Examples.cut_derives_resume_contract
#print axioms Ash.OneShot.OwnerCaptureContracts.Examples.introduced_map
#print axioms Ash.OneShot.OwnerCaptureContracts.Examples.after_capture_source
#print axioms Ash.OneShot.OwnerCaptureContracts.Examples.actual_capture
#print axioms Ash.OneShot.OwnerCaptureContracts.Examples.after_resume_source
#print axioms Ash.OneShot.OwnerCaptureContracts.Examples.capture_then_resume_evidence
#print axioms Ash.OneShot.OwnerCaptureContracts.Examples.duplicate_insertion_not_extension
#print axioms Ash.OneShot.OwnerCaptureContracts.Examples.waiting_handler_changes_residual
