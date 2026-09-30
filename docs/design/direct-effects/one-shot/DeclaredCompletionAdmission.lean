import DeclaredReturnAdmission
import CompletionFrames
import DeclaredSourceResumption
import DeclaredSourceDisposal
import ResumeOnlyCapture
import CheckedCaptureBudgets
import RecursiveOutward

/-! Join hereditary source evidence to the existing structural higher-order
result contracts. The latter already include cleanup and disposal. Resource
entry uses their body derivation, without requiring finite template inference.
All transport below reuses established source and result proofs. -/
namespace Ash.OneShot.DeclaredCompletionAdmission
open ScopedExpressions ScopedExecution CoherentSourceTypes
open DeclaredSourceStates (CheckedState)
open CompletionFrames (ConfigurationReturns)

/-- Initial structural source, requirement and result checks establish all
existing runtime invariant fields. The finite free-resource check rules out
references to activations that have not been issued. Future capture admission
is not asserted by this initial-state construction. -/
theorem initial_state
    (source : DeclaredSources.Expression operations policy (fun _ => none) [] outgoing .none Environment.empty
      code output demand requirements)
    (checked : RecursiveRequirements.Checked [] [] (OwnerPhaseTransitions.available []) requirements row)
    (accepted : ProtectionContracts.checkFootprint outside row = true)
    (result : CompletionContracts.Derives declarations CallableContracts.Environment.empty [] .none code bound)
    (signature : operations.ports = DeclarationResults.signature declarations)
    (support : decide (Syntax.resourceDependencies code.dependencies = []) = true) :
    demand = [] ∧
    CheckedState operations policy (fun _ => none) tables [] outside .none code .nil output [] row ∧
    CompletionJoint.Valid declarations policy (fun _ => none) []
      ⟨⟨⟨code, .none, .nil⟩, [], []⟩, []⟩ output.port outgoing bound := by
  have erased := DeclaredSources.expression_erase source
  obtain ⟨raw, outward, empty, exported, uniform⟩ := RecursiveOutward.checked_source_summary erased checked
  subst demand
  refine ⟨rfl, ?_, ?_⟩
  · have current : RecursiveRequirements.Checked [] [] (OwnerPhaseTransitions.available [])
        (requirements.prepend []) row :=
      RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [List.nil_append] using checked)
    have pending : RecursiveRequirements.Checked [] [] (OwnerPhaseTransitions.available [])
        (RecursiveRequirements.Requirements.request [] []) [] := .request rfl
    simpa only [List.append_nil] using
      (CheckedState.checked (tables := tables) (.checked source .none .nil) .nil (by decide)
        (RecursiveRequirements.Checked.sequence current pending) (by simpa only [List.append_nil] using accepted))
  · have typed := SourceTemplates.expression_ports erased ScopedPorts.EffectScope.none
    rw [signature] at typed
    exact CompletionJoint.initial_configuration_valid typed
      (SourceOwnerClosure.expression_usage erased rfl) (of_decide_eq_true support) result

/-- Reuse the established result-capture proof for the actual raw allocation.
The result judgment does not inspect the live frame's port annotations; the
independent source/port judgment checks those annotations. -/
theorem capture_returns_with_interface
    (step : RawStep before after [.ticket owner] [])
    (typed : ScopedPorts.ConfigurationTyped (DeclarationResults.signature declarations) tickets world before output)
    (returns : ConfigurationReturns declarations registry world before bound)
    (fresh : registry owner = none) :
    ∃ record, CallableFrames.RegistryExtends registry (CallableFrames.insert registry owner record) ∧
      ConfigurationReturns declarations (CallableFrames.insert registry owner record) world after bound ∧
      (∃ binder, after.scope = .ticket binder owner) ∧
      ∃ requested operation operand inputPort outputPort resources,
        before.expression = .perform (Instantiation.freezeEffect requested) operation operand ∧
        DeclarationResults.signature declarations requested operation = some (inputPort, outputPort) ∧
        record.input = .storage resources ∧ ClauseResults.PortBound outputPort resources := by
  cases step with
  | capture requested operation parameter binder owner operand body scope whole capture tail handler annotation cut selected closed ready =>
    obtain ⟨currentPort, current, pending⟩ := typed
    cases current with
    | checked scopeTyped codeTyped =>
      obtain ⟨input, known, available, operandTyped⟩ := ScopedPorts.typed_perform_inversion codeTyped
      obtain ⟨raw, record, inputBound, sameInput, boundedInput, extended, result⟩ :=
        CompletionFrames.capture_step cut selected ⟨currentPort, .checked scopeTyped codeTyped, pending⟩
          known closed.1 returns fresh
      obtain ⟨environment, ticket, input, resultScope, resultCode, resultStack⟩ := result
      cases resultStack with
      | live recorded caller saved rest =>
        exact ⟨record, extended, ⟨environment, _, _, resultScope, resultCode,
          .live recorded caller saved rest⟩, ⟨binder, rfl⟩,
          requested, operation, operand, _, _, inputBound, rfl, known, sameInput, boundedInput⟩

theorem capture_returns
    (step : RawStep before after [.ticket owner] [])
    (typed : ScopedPorts.ConfigurationTyped (DeclarationResults.signature declarations) tickets world before output)
    (returns : ConfigurationReturns declarations registry world before bound)
    (fresh : registry owner = none) :
    ∃ record, CallableFrames.RegistryExtends registry (CallableFrames.insert registry owner record) ∧
      ConfigurationReturns declarations (CallableFrames.insert registry owner record) world after bound := by
  obtain ⟨record, extended, next, interface⟩ := capture_returns_with_interface step typed returns fresh
  exact ⟨record, extended, next⟩

/-- One selected non-disposing allocation now preserves source and structural
result evidence for the same successor and the same new owner. -/
theorem resume_only_capture
    (source : CheckedState operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (returns : ConfigurationReturns declarations registry world
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ bound)
    (signature : operations.ports = DeclarationResults.signature declarations)
    (cut : HandlerCut requested whole capture tail handler)
    (isValue : operand.IsValue) (fresh : contracts owner = none) (resultFresh : registry owner = none)
    (noDispose : (ProtectionContracts.lookup operation (tables handler)).map ProtectionContracts.ClauseContract.dispose = some false) :
    ∃ (contract : Owners.Contract) (record : CallableFrames.ResultRecord) (after : Configuration)
      (nextDemand : List Nat) (nextRow : ProtectionContracts.Footprint),
      contract.closeRow = none ∧
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
      CheckedState operations policy (contracts.insert owner contract) tables world outside
        after.scope after.expression after.stack output nextDemand nextRow ∧
      ConfigurationReturns declarations (CallableFrames.insert registry owner record) world after bound ∧
      CallableFrames.RegistryExtends registry (CallableFrames.insert registry owner record) ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack = owner :: ownedTickets whole := by
  obtain ⟨contract, after, nextDemand, nextRow, closeNone, step, next, demand, rowBound, owners⟩ :=
    ResumeOnlyCapture.capture_from_checked_request source cut isValue fresh noDispose
  have typed := DeclaredReturnAdmission.ports source
  rw [signature] at typed
  obtain ⟨record, extended, result⟩ := capture_returns step typed returns resultFresh
  exact ⟨contract, record, after, nextDemand, nextRow, closeNone, step, next, result, extended, demand, rowBound, owners⟩

/-- The same coherent-record construction serves either capture capability.
It retains the operation interface, actual binder permissions, and both old
registry projections without choosing a second allocation. -/
theorem coherent_capture_record {registry : Owners.Registry}
    (source : CheckedState operations policy registry.contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (returns : ConfigurationReturns declarations registry.runtime.results world
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ bound)
    (signature : operations.ports = DeclarationResults.signature declarations)
    (fresh : registry owner = none)
    (step : RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [])
    (sourceInput : ∃ argument, operations requested operation = some (argument, contract.input)) :
    ∃ (record : Owners.Record) (binder : Nat),
      record.annotation = contract ∧ after.scope = .ticket binder owner ∧
      record.runtime.joint.permissions = policy binder ∧
      ConfigurationReturns declarations (registry.insert owner record).runtime.results world after bound ∧
      registry.contracts.Extends (registry.insert owner record).contracts ∧
      CallableJoint.RegistryExtends registry.runtime (registry.insert owner record).runtime := by
  have resultFresh : registry.runtime.results owner = none := by
    simp [Owners.Registry.runtime, CallableJoint.Registry.results, fresh]
  have typed := DeclaredReturnAdmission.ports source
  rw [signature] at typed
  obtain ⟨resultRecord, extended, resultNext, captureScope, actualRequested, actualOperation, actualOperand,
    inputPort, outputPort, resources, expression, operationKnown, inputSame, outputBound⟩ :=
    capture_returns_with_interface step typed returns resultFresh
  change Code.perform (Instantiation.freezeEffect requested) operation operand =
    Code.perform (Instantiation.freezeEffect actualRequested) actualOperation actualOperand at expression
  injection expression with effectSame operationSame operandSame
  have requestedSame := freeze_effect_injective effectSame
  subst actualRequested
  subst actualOperation
  obtain ⟨argument, sourceLookup⟩ := sourceInput
  have sourcePorts := port_lookup sourceLookup
  rw [signature] at sourcePorts
  have portsSame := Prod.mk.inj (Option.some.inj (sourcePorts.symm.trans operationKnown))
  have inputBound : ClauseResults.PortBound contract.input.port resources := by
    rw [portsSame.2]
    exact outputBound
  obtain ⟨binder, scopeSame⟩ := captureScope
  let runtime : CallableJoint.TicketRecord :=
    ⟨⟨contract.ports, policy binder⟩, resultRecord, resources, inputSame, inputBound⟩
  let record : Owners.Record := ⟨contract, runtime, rfl⟩
  obtain ⟨sourceExtension, runtimeExtension⟩ := Owners.registry_extension (record := record) registry fresh
  refine ⟨record, binder, rfl, scopeSame, rfl, ?_, sourceExtension, runtimeExtension⟩
  rw [Owners.registry_insert_runtime, CallableJoint.results_insert]
  exact resultNext


/-- Reuse the existing coherent runtime record. The operation lookup links its
input storage bound to the source input port, and the actual capture supplies
the clause binder whose permissions are stored. -/
theorem coherent_resume_only_capture {registry : Owners.Registry}
    (source : CheckedState operations policy registry.contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (returns : ConfigurationReturns declarations registry.runtime.results world
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ bound)
    (signature : operations.ports = DeclarationResults.signature declarations)
    (cut : HandlerCut requested whole capture tail handler)
    (isValue : operand.IsValue) (fresh : registry owner = none)
    (noDispose : (ProtectionContracts.lookup operation (tables handler)).map ProtectionContracts.ClauseContract.dispose = some false) :
    ∃ (record : Owners.Record) (after : Configuration) (binder : Nat)
      (nextDemand : List Nat) (nextRow : ProtectionContracts.Footprint),
      record.annotation.closeRow = none ∧
      after.scope = .ticket binder owner ∧ record.runtime.joint.permissions = policy binder ∧
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
      CheckedState operations policy (registry.insert owner record).contracts tables world outside
        after.scope after.expression after.stack output nextDemand nextRow ∧
      ConfigurationReturns declarations (registry.insert owner record).runtime.results world after bound ∧
      registry.contracts.Extends (registry.insert owner record).contracts ∧
      CallableJoint.RegistryExtends registry.runtime (registry.insert owner record).runtime ∧
      nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
      ownedTickets after.stack = owner :: ownedTickets whole := by
  have sourceFresh : registry.contracts owner = none := by simp [Owners.Registry.contracts, fresh]
  obtain ⟨contract, after, nextDemand, nextRow, sourceInput, closeNone, step, next, demand, rowBound, owners⟩ :=
    ResumeOnlyCapture.capture_from_checked_request_with_input source cut isValue sourceFresh noDispose
  obtain ⟨record, binder, annotation, scopeSame, permissions, resultNext, sourceExtension, runtimeExtension⟩ :=
    coherent_capture_record source returns signature fresh step sourceInput
  refine ⟨record, after, binder, nextDemand, nextRow, annotation.symm ▸ closeNone, scopeSame, permissions,
    step, ?_, resultNext, sourceExtension, runtimeExtension, demand, rowBound, owners⟩
  rw [Owners.registry_insert_contracts, annotation]
  exact next


/-- Structural disposal and the finite combined-budget check feed the same
coherent allocation used by the non-disposing path. Preparation retains the
actual captured segment and closing template before the checker is applied. -/
theorem coherent_checked_disposal {registry : Owners.Registry}
    (source : CheckedState operations policy registry.contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (returns : ConfigurationReturns declarations registry.runtime.results world
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ bound)
    (signature : operations.ports = DeclarationResults.signature declarations)
    (cut : HandlerCut requested whole capture tail handler)
    (isValue : operand.IsValue) (fresh : registry owner = none)
    (disposal : ClosingAdmission.checkedDisposal capture.erase tail.erase = some erasedPlan) :
    ∃ (plan : List CloseEntry) (raw : ProtectionContracts.Footprint)
      (closingRequirements : RecursiveRequirements.Requirements (OwnerClosingSource.retirements plan))
      (requestRow resumeRow : ProtectionContracts.Footprint),
      makePlan capture = some plan ∧
      DeclaredSourceClosing.PlanTemplate operations policy registry.contracts tables world .none plan raw closingRequirements ∧
      requestRow ⊆ row ∧ resumeRow ⊆ row ∧
      (∃ (input answer : Value) (capDemand : List Nat)
        (capReq : RecursiveRequirements.Requirements capDemand) (capRecords store : RecursiveRequirements.Store),
        DeclaredSourceFrames.Segment operations policy registry.contracts tables world capture input answer capDemand capReq capRecords ∧
        RecursiveRequirements.Checked store (OwnerPhases.ofStack tables tail)
          (OwnerPhaseTransitions.available (ownedTickets whole)) capReq resumeRow) ∧
      ∀ (_ : DeclaredCallbackAdmission.checkClosing (CallableProtectionFrames.contextOf tables tail)
        outside raw (requestRow ++ resumeRow) = true),
        ∃ (record : Owners.Record) (closingRow : ProtectionContracts.Footprint) (after : Configuration)
          (binder : Nat) (nextDemand : List Nat) (nextRow : ProtectionContracts.Footprint),
          record.annotation.resumeRow = resumeRow ∧ record.annotation.closeRow = some closingRow ∧
          ProtectionResiduals.residualize (CallableProtectionFrames.contextOf tables tail) raw = some closingRow ∧
          closingRow ⊆ requestRow ++ resumeRow ∧
          after.scope = .ticket binder owner ∧ record.runtime.joint.permissions = policy binder ∧
          RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
          CheckedState operations policy (registry.insert owner record).contracts tables world outside
            after.scope after.expression after.stack output nextDemand nextRow ∧
          ConfigurationReturns declarations (registry.insert owner record).runtime.results world after bound ∧
          registry.contracts.Extends (registry.insert owner record).contracts ∧
          CallableJoint.RegistryExtends registry.runtime (registry.insert owner record).runtime ∧
          nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
          ownedTickets after.stack = owner :: ownedTickets whole := by
  have sourceFresh : registry.contracts owner = none := by simp [Owners.Registry.contracts, fresh]
  obtain ⟨plan, raw, closingRequirements, requestRow, resumeRow, built, template, requestBound, resumeBound, saved, finish⟩ :=
    CheckedCaptureBudgets.prepare_checked_disposal_with_input source cut isValue sourceFresh disposal
  refine ⟨plan, raw, closingRequirements, requestRow, resumeRow, built, template, requestBound, resumeBound, saved, ?_⟩
  intro admitted
  obtain ⟨contract, closingRow, after, nextDemand, nextRow, sourceInput, resumeSame, closeSame, exported,
    budget, step, next, demand, rowBound, owners⟩ := finish admitted
  obtain ⟨record, binder, annotation, scopeSame, permissions, resultNext, sourceExtension, runtimeExtension⟩ :=
    coherent_capture_record source returns signature fresh step sourceInput
  refine ⟨record, closingRow, after, binder, nextDemand, nextRow, ?_, ?_, exported, budget,
    scopeSame, permissions, step, ?_, resultNext, sourceExtension, runtimeExtension, demand, rowBound, owners⟩
  · rw [annotation]; exact resumeSame
  · rw [annotation]; exact closeSame
  · rw [Owners.registry_insert_contracts, annotation]
    exact next

theorem bind_preserves
    (source : CheckedState operations policy contracts tables world outside scope
      (.bind name value body) stack output demand row)
    (returns : ConfigurationReturns declarations registry world
      ⟨.bind name value body, scope, stack⟩ bound)
    (isValue : value.IsValue) :
    RawStep ⟨.bind name value body, scope, stack⟩ ⟨body.subst name value, scope, stack⟩ [] [] ∧
    CheckedState operations policy contracts tables world outside scope
      (body.subst name value) stack output demand row ∧
    ConfigurationReturns declarations registry world ⟨body.subst name value, scope, stack⟩ bound := by
  obtain ⟨input, current, pending⟩ := DeclaredReturnAdmission.ports source
  cases current with
  | checked scopeTyped typed => cases typed with
    | bind initializer suffix =>
      have closed := ScopedPorts.typed_value_closed initializer isValue
      obtain ⟨step, next⟩ := CompletionFrames.bind_step returns closed (ScopedPorts.typed_suffix_ready suffix)
      exact ⟨step, DeclaredSourceStates.bind_preserves source closed, next⟩

theorem beta_preserves
    (source : CheckedState operations policy contracts tables world outside scope
      (.app (.lambda parameter body) value) stack output demand row)
    (returns : ConfigurationReturns declarations registry world
      ⟨.app (.lambda parameter body) value, scope, stack⟩ bound)
    (isValue : value.IsValue) :
    RawStep ⟨.app (.lambda parameter body) value, scope, stack⟩
      ⟨body.subst parameter value, .none, stack⟩ [] [] ∧
    CheckedState operations policy contracts tables world outside .none
      (body.subst parameter value) stack output demand row ∧
    ConfigurationReturns declarations registry world ⟨body.subst parameter value, .none, stack⟩ bound := by
  obtain ⟨input, current, pending⟩ := DeclaredReturnAdmission.ports source
  cases current with
  | checked scopeTyped typed => cases typed with
    | app function argument admitted =>
      have closed := ScopedPorts.typed_value_closed argument isValue
      obtain ⟨step, next⟩ := CompletionFrames.beta_step returns closed
        (ScopedPorts.typed_value_closed function trivial)
      exact ⟨step, DeclaredSourceStates.beta_preserves source closed, next⟩

theorem resource_entry
    (source : CheckedState operations policy contracts tables world outside scope
      (.resource binder initializer body) stack output demand row)
    (returns : ConfigurationReturns declarations registry world
      ⟨.resource binder initializer body, scope, stack⟩ bound)
    (isValue : initializer.IsValue) :
    ∃ identity payload answer,
      identity ∉ world ∧ initializer = .integer payload ∧
      RawStep ⟨.resource binder initializer body, scope, stack⟩
        ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
          .push (.cell identity payload scope answer) stack⟩ [.resource identity] [] ∧
      CheckedState operations policy contracts tables (world ++ [identity]) outside scope
        (body.instantiate (Instantiation.Environment.empty.bind binder identity))
        (.push (.cell identity payload scope answer) stack) output demand row ∧
      ConfigurationReturns declarations registry (world ++ [identity])
        ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
          .push (.cell identity payload scope answer) stack⟩ bound := by
  obtain ⟨identity, payload, answer, fresh, same, step, next, phases⟩ :=
    DeclaredSourceEntries.resource_preserves source isValue
  subst initializer
  exact ⟨identity, payload, answer, fresh, rfl, step, next,
    (CompletionFrames.resource_step returns fresh).2⟩

theorem leave_resource
    (source : CheckedState operations policy contracts tables world outside scope value
      (.push (.cell identity payload caller answer) stack) output demand row)
    (returns : ConfigurationReturns declarations registry world
      ⟨value, scope, .push (.cell identity payload caller answer) stack⟩ bound)
    (isValue : value.IsValue) :
    RawStep ⟨value, scope, .push (.cell identity payload caller answer) stack⟩
      ⟨value, caller, stack⟩ [] [.resource identity] ∧
    identity ∉ Syntax.resourceDependencies value.dependencies ∧
    CheckedState operations policy contracts tables world outside caller value stack output demand row ∧
    ConfigurationReturns declarations registry world ⟨value, caller, stack⟩ bound := by
  have closed := DeclaredSourceStates.value_closed source isValue
  obtain ⟨step, excluded, next⟩ := CompletionFrames.cell_return_step returns closed
  exact ⟨step, excluded, DeclaredSourceStates.leave_cell source isValue, next⟩

/-- The restored continuation and waiting caller retain the same structural
result contract while the existing source proof accounts for the consumed owner. -/
theorem resume_preserves {front capture tail : Stack}
    (source : CheckedState operations policy contracts tables world outside scope (.resume binder value)
      (front.append (.live owner inputType answerType capture caller tail)) output demand row)
    (returns : ConfigurationReturns declarations registry world
      ⟨.resume binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩ bound)
    (resolved : scope.resolve binder = some owner) (isValue : value.IsValue) :
    ∃ remaining,
      RawStep ⟨.resume binder value, scope, front.append (.live owner inputType answerType capture caller tail)⟩
        ⟨value, scope, capture.append (front.append (.spent owner answerType caller tail))⟩ [] [.ticket owner] ∧
      CheckedState operations policy contracts tables world outside scope value
        (capture.append (front.append (.spent owner answerType caller tail))) output remaining row ∧
      ConfigurationReturns declarations registry world
        ⟨value, scope, capture.append (front.append (.spent owner answerType caller tail))⟩ bound ∧
      demand = owner :: remaining ∧
      OwnerPhaseTransitions.Trace
        (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) [owner]
        (OwnerPhaseTransitions.available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail))))) := by
  have closed := (ContinuationBounds.resume_operand_bound (environment := fun _ => .unknown)
    resolved (DeclaredReturnAdmission.ports source) isValue).1
  obtain ⟨remaining, next, demand, trace⟩ := DeclaredSourceResumption.resume_cut_preserves source resolved closed
  obtain ⟨step, result⟩ := CompletionFrames.resume_step resolved returns closed
  exact ⟨remaining, step, next, result, demand, trace⟩

/-- The existing structural closing plan retains callback and result contracts
through disposal recomposition; the source proof consumes precisely this owner. -/
theorem discard_preserves {front capture tail : Stack}
    (source : CheckedState operations policy contracts tables world outside scope (.discard binder)
      (front.append (.live owner inputType answerType capture caller tail)) output demand row)
    (returns : ConfigurationReturns declarations registry world
      ⟨.discard binder, scope, front.append (.live owner inputType answerType capture caller tail)⟩ bound)
    (resolved : scope.resolve binder = some owner) (built : makePlan capture = some plan) (identity : Nat) :
    let restored := (closeControl scope plan).append
      (.push (.closing identity scope) (front.append (.spent owner answerType caller tail)))
    ∃ remaining,
      RawStep ⟨.discard binder, scope, front.append (.live owner inputType answerType capture caller tail)⟩
        ⟨.unit, scope, restored⟩ [.close identity] [.ticket owner] ∧
      CheckedState operations policy contracts tables world outside scope .unit restored output remaining row ∧
      ConfigurationReturns declarations registry world ⟨.unit, scope, restored⟩ bound ∧
      demand = owner :: remaining ∧
      OwnerPhaseTransitions.Trace
        (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) [owner]
        (OwnerPhaseTransitions.available (ownedTickets restored)) := by
  obtain ⟨remaining, next, demand, trace⟩ := DeclaredSourceDisposal.discard_cut_preserves source resolved built identity
  obtain ⟨step, result⟩ := CompletionFrames.discard_step (closeId := identity) resolved built returns
  exact ⟨remaining, step, next, result, demand, trace⟩

namespace Examples
open DeclaredReturnAdmission.Examples (operations policy contracts tables functionType retaining_source checked_source)
open ResultSummaries.Examples (retainingConstant)

def body : Code := .app (.lambda 2 (.variable 2)) (retainingConstant 8)
def program : Code := .resource 4 (.integer 0) body
def bound : CallableContracts.Contract := .function [8] (.storage []) (.storage [])

theorem source : CheckedState operations policy contracts tables [8] [] .none program .nil functionType [] [] := by
  apply checked_source
  refine Summary.resource (bodyRow := fun _ => []) .integer ?_
    (by simp [functionType, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
    (List.nil_subset _) (List.Subset.refl []) (by intros; rfl)
  intro identity fresh
  apply Summary.app (functionRow := []) (argumentRow := []) (latentRow := []) (latentRequests := [])
  · apply Summary.lambda
    · exact .variable rfl (by simp [functionType, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
    · simp [functionType, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]
  · exact retaining_source (List.mem_append_left _ List.mem_cons_self)
  · exact List.nil_subset _

theorem retaining_contract : CompletionContracts.Derives declarations environment world ticket
    (retainingConstant 8) bound := by
  apply CompletionContracts.Derives.lambda
  · apply CompletionContracts.Derives.bind (input := .storage [8])
    · exact .leaf trivial rfl (.cons (.resource List.mem_cons_self) .nil)
    · exact .leaf trivial rfl .nil
  · exact .cons (.resource List.mem_cons_self) .nil

theorem returns : ConfigurationReturns declarations (fun _ => none) [8] ⟨program, .none, .nil⟩ bound := by
  refine ⟨CallableContracts.Environment.empty, .none, bound, .none, ?_, .nil⟩
  refine CompletionContracts.Derives.resource (input := .storage []) (.leaf trivial rfl .nil) rfl ?_ ?_
  · intro identity fresh
    exact .app (captures := []) (.lambda (.variable rfl) .nil) retaining_contract
  · exact List.Subset.refl _

theorem template_inference_unknown :
    TemplateSupport.check environment [8] body = false := rfl

/-- The body computes the returned function through application. Existing
structural result contracts carry its support through that computation. -/
theorem application_returns :
    ∃ identity answer,
      identity ∉ [8] ∧
      RawStep ⟨program, .none, .nil⟩
        ⟨body, .none, .push (.cell identity 0 .none answer) .nil⟩ [.resource identity] [] ∧
      RawStep ⟨body, .none, .push (.cell identity 0 .none answer) .nil⟩
        ⟨retainingConstant 8, .none, .push (.cell identity 0 .none answer) .nil⟩ [] [] ∧
      RawStep ⟨retainingConstant 8, .none, .push (.cell identity 0 .none answer) .nil⟩
        ⟨retainingConstant 8, .none, .nil⟩ [] [.resource identity] ∧
      identity ∉ Syntax.resourceDependencies (retainingConstant 8).dependencies ∧
      CheckedState operations policy contracts tables ([8] ++ [identity]) [] .none
        (retainingConstant 8) .nil functionType [] [] ∧
      ConfigurationReturns declarations (fun _ => none) ([8] ++ [identity])
        ⟨retainingConstant 8, .none, .nil⟩ bound := by
  obtain ⟨identity, payload, answer, fresh, same, entry, next, nextReturns⟩ :=
    resource_entry source (returns (declarations := declarations)) trivial
  have payloadZero : payload = 0 := by simpa using same.symm
  subst payload
  change CheckedState _ _ _ _ _ _ _ body _ _ _ _ at next
  change ConfigurationReturns _ _ _ ⟨body, .none, _⟩ _ at nextReturns
  obtain ⟨beta, applied, appliedReturns⟩ := beta_preserves next nextReturns (by trivial)
  obtain ⟨release, excluded, finalSource, finalReturns⟩ := leave_resource applied appliedReturns (by trivial)
  exact ⟨identity, answer, fresh, entry, beta, release, excluded, finalSource, finalReturns⟩

end Examples

end Ash.OneShot.DeclaredCompletionAdmission

#print axioms Ash.OneShot.DeclaredCompletionAdmission.bind_preserves
#print axioms Ash.OneShot.DeclaredCompletionAdmission.beta_preserves
#print axioms Ash.OneShot.DeclaredCompletionAdmission.resource_entry
#print axioms Ash.OneShot.DeclaredCompletionAdmission.leave_resource

#print axioms Ash.OneShot.DeclaredCompletionAdmission.Examples.source

#print axioms Ash.OneShot.DeclaredCompletionAdmission.Examples.retaining_contract

#print axioms Ash.OneShot.DeclaredCompletionAdmission.Examples.returns

#print axioms Ash.OneShot.DeclaredCompletionAdmission.Examples.template_inference_unknown

#print axioms Ash.OneShot.DeclaredCompletionAdmission.Examples.application_returns

#print axioms Ash.OneShot.DeclaredCompletionAdmission.resume_preserves
#print axioms Ash.OneShot.DeclaredCompletionAdmission.discard_preserves

#print axioms Ash.OneShot.DeclaredCompletionAdmission.capture_returns
#print axioms Ash.OneShot.DeclaredCompletionAdmission.resume_only_capture

#print axioms Ash.OneShot.DeclaredCompletionAdmission.capture_returns_with_interface
#print axioms Ash.OneShot.DeclaredCompletionAdmission.coherent_resume_only_capture

#print axioms Ash.OneShot.DeclaredCompletionAdmission.coherent_capture_record
#print axioms Ash.OneShot.DeclaredCompletionAdmission.coherent_checked_disposal

#print axioms Ash.OneShot.DeclaredCompletionAdmission.initial_state
