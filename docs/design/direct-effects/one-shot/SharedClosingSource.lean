import SharedSourceSegments

/-!
Executable close plans obtain shared callback annotations and retirement
records from the recursively checked capture. The same plan determines its
ordinary outward effects and protected source footprint. This component does
not yet authenticate every stored closing field or all call-site phase changes.
-/

namespace Ash.OneShot.SharedClosingSource
open ScopedExpressions ScopedExecution ProtectionContracts CoherentSourceTypes
open OwnerPhaseTransitions (Phases Trace)
open CoherentSourceTypes.Owners (Contracts)
open OwnerClosingSource (retirements)

inductive Contents (operations : Operations) (contracts : Contracts) (world : List Nat) : List CloseEntry → Prop where
  | nil : Contents operations contracts world []
  | release (rest : Contents operations contracts world tail) : Contents operations contracts world (.release identity payload :: tail)
  | retire (known : contracts owner = some contract) (rest : Contents operations contracts world tail) :
      Contents operations contracts world (.retire owner :: tail)
  | invoke (callback : Summary operations world Environment.empty [] action.action (.function .unit .unit action.requests latent) [])
      (rest : Contents operations contracts world tail) : Contents operations contracts world (.invoke action :: tail)

theorem contents_append (first : Contents operations contracts world before) (second : Contents operations contracts world after) :
    Contents operations contracts world (before ++ after) := by
  induction first with
  | nil => exact second
  | release rest ih => exact .release ih
  | retire known rest ih => exact .retire known ih
  | invoke callback rest ih => exact .invoke callback ih

theorem plan_contents
    (segment : SharedSourceSegments.Segment operations policy contracts tables world fixed capture before input after output demand row)
    (built : makePlan capture = some plan) : Contents operations contracts world plan := by
  induction capture generalizing fixed before input after output demand row plan with
  | nil => cases built; exact .nil
  | push frame rest ih => cases segment with
      | push head tail => cases frame with
          | plain => exact ih tail built
          | handler => exact ih tail built
          | cell identity payload scope answer =>
              cases next : makePlan rest <;> simp [makePlan, next] at built
              case some suffix => subst plan; exact .release (ih tail next)
          | armed action => cases head with
              | armed scopeKnown callback annotation exported =>
                  cases next : makePlan rest <;> simp [makePlan, next] at built
                  case some suffix => subst plan; exact .invoke callback (ih tail next)
          | running | unwinding | closing | retiring => simp [makePlan] at built
  | live owner inputType answerType capture scope rest ihSaved ihRest => cases segment with
      | live known inputAnnotation answerAnnotation scopeKnown held consumed saved covered tail =>
          cases inside : makePlan capture <;> cases outside : makePlan rest <;> simp [makePlan, inside, outside] at built
          case some.some first second =>
            subst plan
            exact contents_append (ihSaved saved inside) (.retire known (ihRest tail outside))
  | spent owner answer scope rest ih => cases segment with
      | spent known answerAnnotation scopeKnown consumed tail => exact ih tail built

inductive Rows (operations : Operations) (contracts : Contracts) (world : List Nat) : List CloseEntry → Footprint → Prop where
  | nil : Rows operations contracts world [] []
  | release (rest : Rows operations contracts world tail row) : Rows operations contracts world (.release identity payload :: tail) row
  | retire (known : contracts owner = some contract) (rest : Rows operations contracts world tail row) :
      Rows operations contracts world (.retire owner :: tail) row
  | invoke (callback : Summary operations world Environment.empty [] action.action (.function .unit .unit action.requests latent) [])
      (rest : Rows operations contracts world tail row) :
      Rows operations contracts world (.invoke action :: tail) (DisposalProtection.callbackResidual tail latent ++ row)

theorem contents_rows (contents : Contents operations contracts world plan) : ∃ row, Rows operations contracts world plan row := by
  induction contents with
  | nil => exact ⟨[], .nil⟩
  | release rest ih => obtain ⟨row, rows⟩ := ih; exact ⟨row, .release rows⟩
  | retire known rest ih => obtain ⟨row, rows⟩ := ih; exact ⟨row, .retire known rows⟩
  | invoke callback rest ih => obtain ⟨row, rows⟩ := ih; exact ⟨_, .invoke callback rows⟩

theorem plan_rows
    (segment : SharedSourceSegments.Segment operations policy contracts tables world fixed capture before input after output demand row)
    (built : makePlan capture = some plan) : ∃ raw, Rows operations contracts world plan raw :=
  contents_rows (plan_contents segment built)

theorem rows_protection (rows : Rows operations contracts world plan row) :
    DisposalProtection.Rows operations.protection plan row := by
  induction rows with
  | nil => exact .nil
  | release rest ih => exact .release ih
  | retire known rest ih => exact .retire ih
  | invoke callback rest ih => exact .invoke (protection_summary callback) ih

/-- Ordinary outward effects are computed from each callback's actual suffix.
    A resource released before an invocation cannot discharge its requests. -/
def effects : List CloseEntry → List Instance
  | [] => []
  | .release _ _ :: rest | .retire _ :: rest => effects rest
  | .invoke action :: rest => (action.requests.filter fun request => decide (request ∉ ScopedPorts.planProvides rest)) ++ effects rest

theorem plan_typed_weaken (typed : ScopedPorts.PlanTyped signature world before plan) (larger : before ⊆ after) :
    ScopedPorts.PlanTyped signature world after plan := by
  induction typed with
  | nil => exact .nil
  | release rest ih => exact .release ih
  | retire rest ih => exact .retire ih
  | invoke callback admitted rest ih =>
      refine .invoke callback ?_ ih
      intro request member
      rcases List.mem_append.mp (admitted member) with supplied | outside
      · exact List.mem_append_left _ supplied
      · exact List.mem_append_right _ (larger outside)

theorem rows_ports (rows : Rows operations contracts world plan row) :
    ScopedPorts.PlanTyped operations.ports world (effects plan) plan := by
  induction rows with
  | nil => exact .nil
  | release rest ih => exact .release ih
  | retire known rest ih => exact .retire ih
  | @invoke latent tail raw action callback rest ih =>
      refine .invoke (port_typing callback .none) ?_ (plan_typed_weaken ih (by intro request member; exact List.mem_append_right _ member))
      intro request member
      by_cases provided : request ∈ ScopedPorts.planProvides tail
      · exact List.mem_append_left _ provided
      · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_filter.mpr ⟨member, by simpa using provided⟩))

theorem plan_source
    (rows : Rows operations contracts world plan raw)
    (scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types scope)
    (transition : Trace before (retirements plan) after)
    (separate : ∀ owner ∈ retirements plan, owner ∉ OwnerPhases.names (OwnerPhases.ofStack tables fixed))
    (exported : OwnerSource.exportAt (OwnerPhases.ofStack tables fixed) before raw = some row) :
    SharedSourceSegments.Segment operations policy contracts tables world fixed (closeControl scope plan)
      before .unit after .unit (retirements plan) row := by
  induction rows generalizing before after row with
  | nil =>
      cases transition
      simp only [OwnerSource.exportAt, ProtectionResiduals.residual_empty] at exported
      cases exported
      exact .nil
  | release rest ih => exact .push (.cell scopeKnown (by simp [ScopedPorts.eraseType, ScopedPorts.Port.resources]) rfl) (ih transition separate exported)
  | retire known rest ih =>
      cases transition with
      | cons ready remaining =>
          have tailSeparate := fun owner member => separate owner (List.mem_cons_of_mem _ member)
          have moved := (OwnerClosingSource.suffix_spend (separate _ List.mem_cons_self)).trans exported
          exact .push (.retiring known (.cons ready .nil)) (ih remaining tailSeparate moved)
  | @invoke latent rest raw action callback tail ih =>
      obtain ⟨callbackRow, restRow, callbackExport, restExport, same⟩ := OwnerSource.split_export exported
      rw [same]
      exact .push (.armed (action := { action with scope := scope, answer := .unit }) scopeKnown callback rfl
        (OwnerClosingSource.callback_export callbackExport)) (ih transition separate restExport)

theorem source_consumed
    (source : Owners.Derives operations policy contracts inside world environment allowed scope before code after result demand row)
    (spent : before owner = .consumed) : after owner = .consumed :=
  OwnerPhaseTransitions.trace_monotone (Owners.source_trace source) spent

theorem source_inside_spent
    (source : Owners.Derives operations policy contracts first world environment allowed scope before code after result demand row)
    (spent : before owner = .consumed)
    (same : ∀ phases, phases owner = .consumed → ∀ raw, OwnerSource.exportAt first phases raw = OwnerSource.exportAt second phases raw) :
    Owners.Derives operations policy contracts second world environment allowed scope before code after result demand row := by
  induction source with
  | stable summary exported => exact .stable summary ((same _ spent _).symm.trans exported)
  | pair left right ihLeft ihRight => exact .pair (ihLeft spent) (ihRight (source_consumed left spent))
  | app function argument admitted exported ihFunction ihArgument =>
      have middle := source_consumed function spent
      exact .app (ihFunction spent) (ihArgument middle) admitted ((same _ (source_consumed argument middle) _).symm.trans exported)
  | bind initializer body ihInit ihBody => exact .bind (ihInit spent) (ihBody (source_consumed initializer spent))
  | branch condition yes no ihCondition ihYes ihNo =>
      have middle := source_consumed condition spent
      exact .branch (ihCondition spent) (ihYes middle) (ihNo middle)
  | perform known admitted operand formed exported ih =>
      exact .perform known admitted (ih spent) formed ((same _ (source_consumed operand spent) _).symm.trans exported)
  | resume known resolved permission operand transition admitted formed ih => exact .resume known resolved permission (ih spent) transition admitted formed
  | discard known resolved permission unprotected closable transition admitted => exact .discard known resolved permission unprotected closable transition admitted
  | cleanup callback body admitted exported ihCallback ihBody =>
      have middle := source_consumed callback spent
      apply Owners.Derives.cleanup (ihCallback spent) (ihBody middle) admitted
      simp only [ProtectionResiduals.residualize, DisposalProtection.through_barrier] at exported ⊢
      exact (same _ (source_consumed body middle) _).symm.trans exported
  | resource initializer body formed effectsBound admitted outward exported ih =>
      exact .resource (ih spent) body formed effectsBound admitted outward
        ((same _ (source_consumed initializer spent) _).symm.trans exported)

theorem context_inside_spent
    (context : SharedSourceSegments.Context operations policy contracts first world environment allowed scope position before input after output demand row)
    (spent : before owner = .consumed)
    (same : ∀ phases, phases owner = .consumed → ∀ raw, OwnerSource.exportAt first phases raw = OwnerSource.exportAt second phases raw) :
    SharedSourceSegments.Context operations policy contracts second world environment allowed scope position before input after output demand row := by
  cases context with
  | pairLeft right => exact .pairLeft (source_inside_spent right spent same)
  | pairRight left => exact .pairRight left
  | appFunction argument admitted exported =>
      exact .appFunction (source_inside_spent argument spent same) admitted ((same _ (source_consumed argument spent) _).symm.trans exported)
  | appArgument function admitted exported => exact .appArgument function admitted ((same _ spent _).symm.trans exported)
  | bind body => exact .bind (source_inside_spent body spent same)
  | branch yes no => exact .branch (source_inside_spent yes spent same) (source_inside_spent no spent same)
  | perform known admitted formed exported => exact .perform known admitted formed ((same _ spent _).symm.trans exported)
  | resume known resolved permission transition admitted formed => exact .resume known resolved permission transition admitted formed
  | cleanup body admitted exported =>
      apply SharedSourceSegments.Context.cleanup (source_inside_spent body spent same) admitted
      simp only [ProtectionResiduals.residualize, DisposalProtection.through_barrier] at exported ⊢
      exact (same _ (source_consumed body spent) _).symm.trans exported
  | resource body formed effectsBound admitted outward exported =>
      exact .resource body formed effectsBound admitted outward ((same _ spent _).symm.trans exported)

theorem frame_inside_spent
    (frame : SharedSourceSegments.Frame operations policy contracts first world entry before input after output demand row)
    (spent : before owner = .consumed)
    (same : ∀ phases, phases owner = .consumed → ∀ raw, OwnerSource.exportAt first phases raw = OwnerSource.exportAt second phases raw) :
    SharedSourceSegments.Frame operations policy contracts second world entry before input after output demand row := by
  cases frame with
  | plain source scopeTyped inputAnnotation outputAnnotation => exact .plain (context_inside_spent source spent same) scopeTyped inputAnnotation outputAnnotation
  | handler typed annotation => exact .handler typed annotation
  | cell scopeKnown noEscape annotation => exact .cell scopeKnown noEscape annotation
  | armed scopeKnown callback annotation exported => exact .armed scopeKnown callback annotation ((same _ spent _).symm.trans exported)
  | running scopeKnown callback saved annotation => exact .running scopeKnown callback saved annotation
  | closing scopeKnown => exact .closing scopeKnown
  | retiring known transition => exact .retiring known transition

theorem segment_fixed_spent
    (segment : SharedSourceSegments.Segment operations policy contracts tables world first stack before input after output demand row)
    (spent : before owner = .consumed)
    (same : ∀ phases, phases owner = .consumed →
      OwnerPhaseTransitions.project (OwnerPhases.ofStack tables first) phases = OwnerPhaseTransitions.project (OwnerPhases.ofStack tables second) phases) :
    SharedSourceSegments.Segment operations policy contracts tables world second stack before input after output demand row := by
  induction stack generalizing before input after output demand row with
  | nil => cases segment; exact .nil
  | push entry rest ih => cases segment with
      | push head tail =>
          exact .push (frame_inside_spent head spent (fun phases done raw => OwnerSourceResumption.export_prefix_spent _ same done))
            (ih tail (OwnerPhaseTransitions.trace_monotone (OwnerSource.frame_trace (SharedSourceSegments.frame_source head)) spent))
  | live owner inputType answerType capture scope rest ihCapture ihRest => cases segment with
      | live known inputAnnotation answerAnnotation scopeKnown held consumed saved covered tail =>
          exact .live known inputAnnotation answerAnnotation scopeKnown held consumed saved covered (ihRest tail spent)
  | spent owner answer scope rest ih => cases segment with
      | spent known answerAnnotation scopeKnown consumed tail => exact .spent known answerAnnotation scopeKnown consumed (ih tail spent)

section Disposal
variable {front capture tail fixed : Stack}

theorem pending_live_to_spent
    (segment : SharedSourceSegments.Segment operations policy contracts tables world fixed
      (front.append (.live owner inputType answerType capture caller tail)) before input after output demand row)
    (spent : before owner = .consumed) :
    SharedSourceSegments.Segment operations policy contracts tables world fixed
      (front.append (.spent owner answerType caller tail)) before input after output demand row := by
  obtain ⟨phases, intermediate, firstDemand, secondDemand, firstRow, secondRow, first, second, names, effects⟩ :=
    SharedSourceSegments.segment_decompose (front := front) segment
  cases second with
  | live known inputAnnotation answerAnnotation scopeKnown held consumed saved covered rest =>
      have changed := segment_fixed_spent first spent (fun phases done => OwnerSourceResumption.live_spent_project
        (tables := tables) (capture := capture) (caller := caller) (inputType := inputType)
        (answerType := answerType) (tail := tail.append fixed) done)
      rw [names, effects]
      exact SharedSourceSegments.segment_append changed (.spent known answerAnnotation scopeKnown consumed rest)

theorem selected_plan_rows
    (segment : SharedSourceSegments.Segment operations policy contracts tables world fixed
      (front.append (.live owner inputType answerType capture caller tail)) before input after output demand row)
    (built : makePlan capture = some plan) : ∃ raw, Rows operations contracts world plan raw := by
  obtain ⟨phases, intermediate, firstDemand, secondDemand, firstRow, secondRow, first, second, names, effects⟩ :=
    SharedSourceSegments.segment_decompose (front := front) segment
  cases second with
  | live known inputAnnotation answerAnnotation scopeKnown held consumed saved covered rest => exact plan_rows saved built

theorem discard_parts
    (source : SharedSourceSegments.Source operations policy contracts tables world fixed outside scope (.discard binder) stack before after output demand row)
    (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner) :
    ∃ middle bound remaining restRow,
      ScopedPorts.EffectScopeKnown contracts.ports scope ∧ contract.held = false ∧ contract.closeRow = some bound ∧
      Trace before (owner :: contract.closeDemand) middle ∧
      SharedSourceSegments.Segment operations policy contracts tables world fixed stack middle .unit after output remaining restRow ∧
      demand = owner :: (contract.closeDemand ++ remaining) ∧ row = bound ++ restRow ∧ checkFootprint outside row = true := by
  cases source with
  | checked current scopeTyped pending accepted => cases current with
      | stable summary exported => cases summary
      | discard actual target permission unprotected closable transition admitted =>
          have ownerSame := Option.some.inj (target.symm.trans resolved)
          subst_vars
          have contractSame := Option.some.inj (actual.symm.trans known)
          subst_vars
          exact ⟨_, _, _, _, ⟨_, scopeTyped⟩, unprotected, closable, transition, pending, rfl, rfl, accepted⟩

theorem selected_unprotected
    (segment : SharedSourceSegments.Segment operations policy contracts tables world fixed
      (front.append (.live owner inputType answerType capture caller tail)) before input after output demand row)
    (known : contracts owner = some contract) (unprotected : contract.held = false) :
    ProtectionContexts.protectedMode capture.erase = false := by
  obtain ⟨phases, intermediate, firstDemand, secondDemand, firstRow, secondRow, first, second, names, effects⟩ :=
    SharedSourceSegments.segment_decompose (front := front) segment
  cases second with
  | live actual inputAnnotation answerAnnotation scopeKnown held consumed saved covered rest =>
      have same := Option.some.inj (actual.symm.trans known)
      subst_vars
      exact held.symm.trans unprotected

theorem disposal_plan
    (source : SharedSourceSegments.Source operations policy contracts tables world fixed outside scope (.discard binder)
      (front.append (.live owner inputType answerType capture caller tail)) before after output demand row)
    (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner) :
    ∃ plan raw, makePlan capture = some plan ∧ Rows operations contracts world plan raw ∧
      ScopedPorts.PlanTyped operations.ports world (effects plan) plan ∧
      (retirements plan).Perm (ownedTickets capture) := by
  obtain ⟨middle, bound, remaining, restRow, scopeKnown, unprotected, closable, transition, pending, names, rows, accepted⟩ :=
    discard_parts source known resolved
  have mode := selected_unprotected pending known unprotected
  have available := CaptureInterfaces.plan_available capture
  rw [mode] at available
  cases built : makePlan capture with
  | none => simp [built] at available
  | some plan =>
      obtain ⟨raw, checked⟩ := selected_plan_rows pending built
      exact ⟨plan, raw, rfl, checked, rows_ports checked, OwnerClosingSource.retirements_capture built⟩

/-- The after-source is reconstructed from the actual plan and waiting stack.
    Recorded closing bounds and separation are still checked premises. -/
theorem discard_source
    (source : SharedSourceSegments.Source operations policy contracts tables world fixed outside scope (.discard binder)
      (front.append (.live owner inputType answerType capture caller tail)) before after output demand row)
    (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
    (built : makePlan capture = some plan) (closingNames : contract.closeDemand = retirements plan)
    (ordinaryBound : effects plan ⊆ contract.closeEffects)
    (separate : ∀ nested ∈ retirements plan, nested ∉ OwnerPhases.names (OwnerPhases.ofStack tables
      ((Stack.push (.closing closeId scope) (front.append (.spent owner answerType caller tail))).append fixed))) :
    ∃ raw bound remaining restRow,
      Rows operations contracts world plan raw ∧ ScopedPorts.PlanTyped operations.ports world contract.closeEffects plan ∧
      contract.closeRow = some bound ∧ demand = owner :: (contract.closeDemand ++ remaining) ∧ row = bound ++ restRow ∧
      (∀ actual, OwnerSource.exportAt (OwnerPhases.ofStack tables
          ((Stack.push (.closing closeId scope) (front.append (.spent owner answerType caller tail))).append fixed))
          (OwnerPhaseTransitions.spend before owner) raw = some actual →
        EffectBounds.Covers bound actual →
        RawStep ⟨.discard binder, scope, front.append (.live owner inputType answerType capture caller tail)⟩
          ⟨.unit, scope, (closeControl scope plan).append (.push (.closing closeId scope) (front.append (.spent owner answerType caller tail)))⟩
          [.close closeId] [.ticket owner] ∧
        SharedSourceSegments.Source operations policy contracts tables world fixed outside scope .unit
          ((closeControl scope plan).append (.push (.closing closeId scope) (front.append (.spent owner answerType caller tail))))
          (OwnerPhaseTransitions.spend before owner) after output (contract.closeDemand ++ remaining) (actual ++ restRow)) := by
  obtain ⟨middle, bound, remaining, restRow, scopes, unprotected, closable, transition, pending, names, rows, accepted⟩ :=
    discard_parts source known resolved
  obtain ⟨raw, checked⟩ := selected_plan_rows pending built
  have scopeKnown := ScopedPorts.effect_scope_known_has_types scopes
  obtain ⟨ticket, scopeTyped⟩ := scopes
  refine ⟨raw, bound, remaining, restRow, checked, plan_typed_weaken (rows_ports checked) ordinaryBound,
    closable, names, rows, ?_⟩
  intro actual exported covered
  have consumed := OwnerPhaseTransitions.trace_consumed transition List.mem_cons_self
  have changed := pending_live_to_spent pending consumed
  have plannedTrace : Trace (OwnerPhaseTransitions.spend before owner) (retirements plan) middle := by
    cases transition with
    | cons ready rest => simpa only [closingNames] using rest
  have planned := plan_source (policy := policy) checked scopeKnown plannedTrace separate exported
  have closing := SharedSourceSegments.Segment.push (SharedSourceSegments.Frame.closing (identity := closeId) scopeKnown) changed
  have composed := SharedSourceSegments.segment_append planned closing
  have acceptedActual := EffectBounds.check_covered (rows ▸ accepted)
    (EffectBounds.covers_append_bounds covered (EffectBounds.covers_refl restRow))
  have current : Owners.Derives operations policy contracts
      (OwnerPhases.ofStack tables (((closeControl scope plan).append (.push (.closing closeId scope)
        (front.append (.spent owner answerType caller tail)))).append fixed)) world Environment.empty [] scope
      (OwnerPhaseTransitions.spend before owner) .unit (OwnerPhaseTransitions.spend before owner) .unit [] [] :=
    .stable .unit (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])
  have restored := SharedSourceSegments.Source.checked current scopeTyped composed acceptedActual
  exact ⟨.discard binder owner closeId scope caller inputType answerType front capture tail plan resolved built,
    by simpa only [closingNames, List.nil_append] using restored⟩

/-- The ordinary plan proof comes from the same shared callbacks as the
    source footprint. Runtime history derives suffix separation and the
    actual after-phase map; no independent plan typing is supplied. -/
theorem discard_joint
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.discard binder, scope, front.append (.live owner inputType answerType capture caller tail)⟩,
        issued, completed⟩, activations⟩ result outgoing callableBound)
    (signatures : operations.ports = DeclarationResults.signature declarations)
    (registrySame : contracts.ports = registry.joint.effects)
    (source : SharedSourceSegments.Source operations policy contracts tables (ScopedTyping.resourceWorld issued) .nil outside scope (.discard binder)
      (front.append (.live owner inputType answerType capture caller tail))
      (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture caller tail))))
      finalPhase output demand row)
    (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
    (built : makePlan capture = some plan) (closingNames : contract.closeDemand = retirements plan)
    (ordinaryBound : effects plan ⊆ contract.closeEffects)
    (fresh : (issued ++ [Owner.close closeId]).Nodup)
    (checks : AccessChecks ⟨.discard binder, scope, front.append (.live owner inputType answerType capture caller tail)⟩ ambient) :
    ∃ raw bound remaining restRow,
      Rows operations contracts (ScopedTyping.resourceWorld issued) plan raw ∧
      contract.closeRow = some bound ∧ demand = owner :: (contract.closeDemand ++ remaining) ∧ row = bound ++ restRow ∧
      (∀ actual, OwnerSource.exportAt (OwnerPhases.ofStack tables
          (.push (.closing closeId scope) (front.append (.spent owner answerType caller tail))))
          (OwnerPhaseTransitions.spend (OwnerPhaseTransitions.available
            (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) owner) raw = some actual →
        EffectBounds.Covers bound actual →
        let before : NamedState := ⟨⟨⟨.discard binder, scope, front.append (.live owner inputType answerType capture caller tail)⟩,
          issued, completed⟩, activations⟩
        let after : Configuration := ⟨.unit, scope, (closeControl scope plan).append
          (.push (.closing closeId scope) (front.append (.spent owner answerType caller tail)))⟩
        NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [.close closeId] [.ticket owner]) ∧
        CompletionJoint.Valid declarations policy registry ambient
          (ScopedPortJoint.advanceState before after [.close closeId] [.ticket owner]) result outgoing callableBound ∧
        Trace (OwnerPhaseTransitions.available (ownedTickets before.execution.configuration.stack)) [owner]
          (OwnerPhaseTransitions.available (ownedTickets after.stack)) ∧
        SharedSourceSegments.Source operations policy contracts tables (ScopedTyping.resourceWorld issued) .nil outside scope .unit after.stack
          (OwnerPhaseTransitions.available (ownedTickets after.stack)) finalPhase output (contract.closeDemand ++ remaining) (actual ++ restRow)) := by
  have distinct := (history_gives_distinct_names valid.joint.names valid.joint.ledger).1
  have separate := OwnerClosingSource.retirements_separate (tables := tables) (closeId := closeId) (scope := scope) distinct built
  obtain ⟨raw, bound, remaining, restRow, rows, typed, closable, names, effects, restore⟩ :=
    discard_source source known resolved built closingNames ordinaryBound
      (by simpa only [OwnerSourceResumption.stack_append_empty] using separate)
  refine ⟨raw, bound, remaining, restRow, rows, closable, names, effects, ?_⟩
  intro actual exported covered
  obtain ⟨rawStep, restored⟩ := restore actual
    (by simpa only [OwnerSourceResumption.stack_append_empty] using exported) covered
  obtain ⟨_, _, _, _, _, _, unique⟩ := valid.joint.usage
  have transition := OwnerClosingSource.discard_phase_trace (scope := scope) (closeId := closeId) built unique
  have phases := OwnerPhaseTransitions.trace_result transition
  change OwnerPhaseTransitions.available (ownedTickets ((closeControl scope plan).append
    (.push (.closing closeId scope) (front.append (.spent owner answerType caller tail))))) =
      OwnerPhaseTransitions.spend (OwnerPhaseTransitions.available
        (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) owner at phases
  have runtimeKnown := registrySame ▸ Owners.ports_lookup known
  obtain ⟨step, preserved⟩ := CompletionJoint.discard_preserves valid runtimeKnown resolved built
    (signatures ▸ typed) fresh checks
  exact ⟨step, preserved, transition, phases.symm ▸ restored⟩

end Disposal

theorem scope_effects {contracts : Contracts} (known : ScopedPorts.ScopeKnown contracts.ports.types scope) :
    ScopedPorts.EffectScopeKnown contracts.ports scope := by
  obtain ⟨ticket, typed⟩ := known
  cases typed with
  | none => exact ⟨.none, .none⟩
  | @bound owner input answer binder residual closing known =>
      cases found : contracts owner with
      | none => simp [ScopedPorts.EffectTickets.types, Owners.Contracts.ports, found] at known
      | some contract => exact ⟨_, .bound (Owners.ports_lookup found)⟩

theorem source_start_cleanup
    (source : SharedSourceSegments.Source operations policy contracts tables world fixed outside scope value (.push (.armed action) tail)
      before after output demand row) (closed : ClosedValue value) :
    SharedSourceSegments.Source operations policy contracts tables world fixed outside .none (.app action.action .unit)
      (.push (.running action value closed) tail) before after output demand row := by
  cases source with
  | checked current scopeTyped pending accepted =>
      obtain ⟨valueSource, same, noDemand, noRow⟩ := Owners.value_summary current closed.1
      subst_vars
      cases pending with
      | push head rest => cases head with
          | armed scopeKnown callback annotation exported =>
              have invocation := Owners.Derives.stable (policy := policy) (contracts := contracts) (scope := Execution.Scope.none)
                (inside := OwnerPhases.ofStack tables ((Stack.push (.running action value closed) tail).append fixed))
                (Summary.app (value_allowed callback action.closed.1 action.requests) Summary.unit (List.Subset.refl _)) (by
                  simpa only [Stack.append, OwnerPhases.ofStack, OwnerPhases.frameEntry, ExecFrame.erase,
                    ProtectionContexts.frameProtected, OwnerPhaseTransitions.project, OwnerSource.exportAt,
                    ProtectionResiduals.residualize, DisposalProtection.through_barrier, List.nil_append] using exported)
              have restored := SharedSourceSegments.Source.checked invocation .none
                (.push (.running scopeKnown callback (value_allowed valueSource closed.1 []) annotation) rest) accepted
              simpa only [List.nil_append] using restored

theorem source_finish_cleanup
    (source : SharedSourceSegments.Source operations policy contracts tables world fixed outside scope .unit (.push (.running action value closed) tail)
      before after output demand row) :
    SharedSourceSegments.Source operations policy contracts tables world fixed outside action.scope value tail before after output demand row := by
  cases source with
  | checked current scopeTyped pending accepted =>
      obtain ⟨summary, same, noDemand, noRow⟩ := Owners.value_summary current trivial
      subst_vars
      cases pending with
      | push head rest => cases head with
          | running scopeKnown callback saved annotation =>
              obtain ⟨ticket, scopeTyped⟩ := scope_effects scopeKnown
              have restored := SharedSourceSegments.Source.checked
                (Owners.Derives.stable (scope := action.scope) (row := []) saved
                  (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])) scopeTyped rest accepted
              simpa only [List.nil_append] using restored

theorem source_finish_close
    (source : SharedSourceSegments.Source operations policy contracts tables world fixed outside scope .unit (.push (.closing closeId caller) tail)
      before after output demand row) :
    SharedSourceSegments.Source operations policy contracts tables world fixed outside caller .unit tail before after output demand row := by
  cases source with
  | checked current scopeTyped pending accepted =>
      obtain ⟨summary, same, noDemand, noRow⟩ := Owners.value_summary current trivial
      subst_vars
      cases pending with
      | push head rest => cases head with
          | closing scopeKnown =>
              obtain ⟨ticket, scopeTyped⟩ := scope_effects scopeKnown
              have restored := SharedSourceSegments.Source.checked
                (Owners.Derives.stable (environment := Environment.empty) (allowed := []) (scope := caller) (row := []) Summary.unit
                  (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])) scopeTyped rest accepted
              simpa only [List.nil_append] using restored

theorem source_retire
    (source : SharedSourceSegments.Source operations policy contracts tables world fixed outside scope .unit (.push (.retiring owner) tail)
      before after output demand row) :
    ∃ remaining, demand = owner :: remaining ∧ before owner = .available ∧
      SharedSourceSegments.Source operations policy contracts tables world fixed outside scope .unit tail
        (OwnerPhaseTransitions.spend before owner) after output remaining row := by
  cases source with
  | checked current scopeTyped pending accepted =>
      obtain ⟨summary, same, noDemand, noRow⟩ := Owners.value_summary current trivial
      subst_vars
      cases pending with
      | push head rest => cases head with
          | retiring known transition => cases transition with
              | cons ready endTrace =>
                  cases endTrace
                  refine ⟨_, rfl, ready, ?_⟩
                  have restored := SharedSourceSegments.Source.checked
                    (Owners.Derives.stable (environment := Environment.empty) (allowed := []) (scope := scope) (row := []) Summary.unit
                      (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])) scopeTyped rest accepted
                  simpa [List.append] using restored

theorem source_leave_cell
    (source : SharedSourceSegments.Source operations policy contracts tables world fixed outside scope value (.push (.cell identity payload caller answerType) tail)
      before after output demand row) (isValue : value.IsValue) :
    SharedSourceSegments.Source operations policy contracts tables world fixed outside caller value tail before after output demand row := by
  cases source with
  | checked current scopeTyped pending accepted =>
      obtain ⟨summary, same, noDemand, noRow⟩ := Owners.value_summary current isValue
      subst_vars
      cases pending with
      | push head rest => cases head with
          | cell scopeKnown noEscape annotation =>
              obtain ⟨ticket, scopeTyped⟩ := scope_effects scopeKnown
              have restored := SharedSourceSegments.Source.checked
                (Owners.Derives.stable (scope := caller) (row := []) summary
                  (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])) scopeTyped rest accepted
              simpa only [List.nil_append] using restored

namespace Examples
open OwnerPhaseTransitions (empty)

def operations : Operations := fun effect operation =>
  if effect = .cell 4 ∧ operation = 0 then some (.reference 4, .integer) else none
def policy : Syntax.TicketPolicy := fun _ => ⟨true, true⟩
def tables : CallableProtectionFrames.Tables := fun _ => []
def contract : Owners.Contract := ⟨.unit, .unit, false, [], [], [], some [], [], []⟩
def contracts : Contracts := fun owner => if owner = 19 then some contract else none
def latent : Footprint := [⟨.cell 4, 0, false⟩]
def callback : Code := .lambda 0 (.bind 1 (.perform (Instantiation.freezeEffect (.cell 4)) 0 (.resourceRef (.activation 4))) .unit)

theorem operation_known : operations (.cell 4) 0 = some (.reference 4, .integer) := by decide
theorem owner_known : contracts 19 = some contract := by decide

theorem callback_shared : Summary operations [4] Environment.empty [] callback (.function .unit .unit [.cell 4] latent) [] := by
  apply Summary.lambda (input := Value.unit) (latentRequests := [.cell 4])
  · exact .bind (.perform operation_known List.mem_cons_self (.reference List.mem_cons_self)
      (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])) .unit
  · simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources, Instance.resources]

def action : ActionData := ⟨7, callback, ScopedPorts.typed_value_closed (port_typing callback_shared .none) trivial, .none, .unit, [.cell 4]⟩
def capture : Stack := .push (.armed action) (.push (.cell 4 17 .none .unit) .nil)
def plan : List CloseEntry := [.invoke action, .release 4 17]
def reversed : List CloseEntry := [.release 4 17, .invoke action]
def nested : Stack := .live 19 .unit .unit capture .none .nil

theorem built : makePlan capture = some plan := rfl

theorem captured_shared : SharedSourceSegments.Segment operations policy contracts tables [4] .nil capture empty .unit empty .unit [] [] := by
  have head : SharedSourceSegments.Frame operations policy contracts
      (OwnerPhases.ofStack tables ((Stack.push (.cell 4 17 .none .unit) .nil).append .nil)) [4]
      (.armed action) empty .unit empty .unit [] [] :=
    .armed (action := action) ⟨.none, .none⟩ callback_shared rfl (by decide)
  exact .push head (.push (.cell ⟨.none, .none⟩ (by simp [ScopedPorts.eraseType, ScopedPorts.Port.resources]) rfl) .nil)

theorem derived_plan : ∃ raw, Rows operations contracts [4] plan raw := plan_rows captured_shared built

theorem rows : Rows operations contracts [4] plan [] :=
  .invoke (action := action) (latent := latent) callback_shared (.release .nil)

theorem reversed_rows : Rows operations contracts [4] reversed [⟨.cell 4, 0, true⟩] :=
  .release (.invoke (action := action) (latent := latent) callback_shared .nil)

theorem outward_order : effects plan = [] ∧ effects reversed = [.cell 4] := by decide
theorem source_order : checkFootprint [] ([] : Footprint) = true ∧ checkFootprint [] [⟨Instance.cell 4, 0, true⟩] = false := by decide
theorem ordinary_bound_rejects_reversal : ¬ effects reversed ⊆ contract.closeEffects := by decide

theorem nested_shared : SharedSourceSegments.Segment operations policy contracts tables [4] .nil nested empty .unit empty .unit [] [] :=
  .live owner_known rfl rfl ⟨.none, .none⟩ rfl rfl captured_shared (EffectBounds.covers_refl []) .nil

theorem owner_transition : Trace (OwnerPhaseTransitions.introduce empty 19) [19] empty := by
  apply Trace.cons (by simp [OwnerPhaseTransitions.introduce])
  rw [OwnerCaptureContracts.spend_introduced (by rfl)]
  exact .nil

theorem before_source : SharedSourceSegments.Source operations policy contracts tables [4] .nil [] (.ticket 7 19) (.discard 7)
    nested (OwnerPhaseTransitions.introduce empty 19) empty .unit [19] [] := by
  have current : Owners.Derives operations policy contracts (OwnerPhases.ofStack tables (nested.append .nil)) [4] Environment.empty [] (.ticket 7 19)
      (OwnerPhaseTransitions.introduce empty 19) (.discard 7) empty .unit [19] [] :=
    .discard owner_known rfl rfl rfl rfl owner_transition (by simp [contract])
  exact .checked current (.bound (Owners.ports_lookup owner_known)) nested_shared (by decide)

def waiting : Stack := .push (.closing 41 (.ticket 7 19)) (.spent 19 .unit .none .nil)
def afterStack : Stack := (closeControl (.ticket 7 19) plan).append waiting

theorem planned_source : SharedSourceSegments.Segment operations policy contracts tables [4] waiting
    (closeControl (.ticket 7 19) plan) empty .unit empty .unit [] [] :=
  plan_source rows ⟨_, ScopedPorts.effect_scope_has_types (.bound (Owners.ports_lookup owner_known))⟩ .nil
    (by intro owner member; cases member) (by decide)

theorem after_segment : SharedSourceSegments.Segment operations policy contracts tables [4] .nil afterStack empty .unit empty .unit [] [] :=
  SharedSourceSegments.segment_append planned_source
    (.push (.closing ⟨_, ScopedPorts.effect_scope_has_types (.bound (Owners.ports_lookup owner_known))⟩)
      (.spent owner_known rfl ⟨.none, .none⟩ rfl .nil))

theorem after_source : SharedSourceSegments.Source operations policy contracts tables [4] .nil [] (.ticket 7 19) .unit
    afterStack empty empty .unit [] [] := by
  have current : Owners.Derives operations policy contracts (OwnerPhases.ofStack tables (afterStack.append .nil)) [4] Environment.empty [] (.ticket 7 19)
      empty .unit empty .unit [] [] := .stable .unit (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])
  exact .checked current (.bound (Owners.ports_lookup owner_known)) after_segment (by decide)

theorem disposal_step : RawStep ⟨.discard 7, .ticket 7 19, nested⟩ ⟨.unit, .ticket 7 19, afterStack⟩ [.close 41] [.ticket 19] ∧
    SharedSourceSegments.Source operations policy contracts tables [4] .nil [] (.ticket 7 19) .unit afterStack empty empty .unit [] [] :=
  ⟨.discard 7 19 41 (.ticket 7 19) .none .unit .unit .nil capture .nil plan rfl built, after_source⟩

def prepared : ActionData := { action with scope := .ticket 7 19, answer := .unit }
def cellTail : Stack := .push (.cell 4 17 (.ticket 7 19) .unit) waiting
def running : Stack := .push (.running prepared .unit CallableProtection.Examples.unit_closed) cellTail

theorem start_source : SharedSourceSegments.Source operations policy contracts tables [4] .nil [] .none (.app callback .unit)
    running empty empty .unit [] [] := source_start_cleanup after_source CallableProtection.Examples.unit_closed

theorem start_step : RawStep ⟨.unit, .ticket 7 19, afterStack⟩ ⟨.app callback .unit, .none, running⟩ [] [] ∧
    SharedSourceSegments.Source operations policy contracts tables [4] .nil [] .none (.app callback .unit) running empty empty .unit [] [] :=
  ⟨.startCleanup prepared .unit CallableProtection.Examples.unit_closed (.ticket 7 19) cellTail, start_source⟩

theorem callback_body_source : SharedSourceSegments.Source operations policy contracts tables [4] .nil [] .none
    (.bind 1 (.perform (Instantiation.freezeEffect (.cell 4)) 0 (.resourceRef (.activation 4))) .unit)
    running empty empty .unit [] [] :=
  SharedSourceSegments.source_beta start_source CallableProtection.Examples.unit_closed

theorem scalar_cleanup_gap : CallableProtection.Summarizes operations.protection CallableProtection.Environment.empty
    (.lambda 0 (.boolean true)) (.function .scalar .scalar []) [] := .lambda .boolean

theorem boolean_cleanup_rejected : ¬ Summary operations [4] Environment.empty []
    (.lambda 0 (.boolean true)) (.function .unit .unit requests raw) [] := by
  intro summary
  cases summary with
  | lambda body formed => cases body

end Examples

end Ash.OneShot.SharedClosingSource

#print axioms Ash.OneShot.SharedClosingSource.contents_append
#print axioms Ash.OneShot.SharedClosingSource.plan_contents
#print axioms Ash.OneShot.SharedClosingSource.contents_rows
#print axioms Ash.OneShot.SharedClosingSource.plan_rows
#print axioms Ash.OneShot.SharedClosingSource.rows_protection
#print axioms Ash.OneShot.SharedClosingSource.plan_typed_weaken
#print axioms Ash.OneShot.SharedClosingSource.rows_ports
#print axioms Ash.OneShot.SharedClosingSource.plan_source
#print axioms Ash.OneShot.SharedClosingSource.source_consumed
#print axioms Ash.OneShot.SharedClosingSource.source_inside_spent
#print axioms Ash.OneShot.SharedClosingSource.context_inside_spent
#print axioms Ash.OneShot.SharedClosingSource.frame_inside_spent
#print axioms Ash.OneShot.SharedClosingSource.segment_fixed_spent
#print axioms Ash.OneShot.SharedClosingSource.pending_live_to_spent
#print axioms Ash.OneShot.SharedClosingSource.selected_plan_rows
#print axioms Ash.OneShot.SharedClosingSource.discard_parts
#print axioms Ash.OneShot.SharedClosingSource.selected_unprotected
#print axioms Ash.OneShot.SharedClosingSource.disposal_plan
#print axioms Ash.OneShot.SharedClosingSource.discard_source
#print axioms Ash.OneShot.SharedClosingSource.discard_joint
#print axioms Ash.OneShot.SharedClosingSource.scope_effects
#print axioms Ash.OneShot.SharedClosingSource.source_start_cleanup
#print axioms Ash.OneShot.SharedClosingSource.source_finish_cleanup
#print axioms Ash.OneShot.SharedClosingSource.source_finish_close
#print axioms Ash.OneShot.SharedClosingSource.source_retire
#print axioms Ash.OneShot.SharedClosingSource.source_leave_cell
#print axioms Ash.OneShot.SharedClosingSource.Examples.operation_known
#print axioms Ash.OneShot.SharedClosingSource.Examples.owner_known
#print axioms Ash.OneShot.SharedClosingSource.Examples.callback_shared
#print axioms Ash.OneShot.SharedClosingSource.Examples.built
#print axioms Ash.OneShot.SharedClosingSource.Examples.captured_shared
#print axioms Ash.OneShot.SharedClosingSource.Examples.derived_plan
#print axioms Ash.OneShot.SharedClosingSource.Examples.rows
#print axioms Ash.OneShot.SharedClosingSource.Examples.reversed_rows
#print axioms Ash.OneShot.SharedClosingSource.Examples.outward_order
#print axioms Ash.OneShot.SharedClosingSource.Examples.source_order
#print axioms Ash.OneShot.SharedClosingSource.Examples.ordinary_bound_rejects_reversal
#print axioms Ash.OneShot.SharedClosingSource.Examples.nested_shared
#print axioms Ash.OneShot.SharedClosingSource.Examples.owner_transition
#print axioms Ash.OneShot.SharedClosingSource.Examples.before_source
#print axioms Ash.OneShot.SharedClosingSource.Examples.planned_source
#print axioms Ash.OneShot.SharedClosingSource.Examples.after_segment
#print axioms Ash.OneShot.SharedClosingSource.Examples.after_source
#print axioms Ash.OneShot.SharedClosingSource.Examples.disposal_step
#print axioms Ash.OneShot.SharedClosingSource.Examples.start_source
#print axioms Ash.OneShot.SharedClosingSource.Examples.start_step
#print axioms Ash.OneShot.SharedClosingSource.Examples.callback_body_source
#print axioms Ash.OneShot.SharedClosingSource.Examples.scalar_cleanup_gap
#print axioms Ash.OneShot.SharedClosingSource.Examples.boolean_cleanup_rejected
