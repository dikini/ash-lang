import DeclaredCallbackAdmission
import ResumeOnlyCapture

/-! Connect the finite closing checker to the actual source cut's resumption
row before allocation. Existing capture assembly supplies the successor; the
checker is not asserted to succeed for every initially typed program. -/
namespace Ash.OneShot.CheckedCaptureBudgets
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts ProtectionResiduals
open DeclaredSourceStates (CheckedState)
open RecursiveRequirements (Requirements Checked Store)
open DeclaredCallbackAdmission (checkClosing)

/-- Source decomposition and structural disposal determine the plan and
resumption budget. A successful finite closing check then supplies the complete
capture successor, with no separate post-allocation row-bound premise. -/
theorem prepare_checked_disposal_with_input
    (source : CheckedState operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (cut : HandlerCut requested whole capture tail handler)
    (isValue : operand.IsValue) (fresh : contracts owner = none)
    (disposal : ClosingAdmission.checkedDisposal capture.erase tail.erase = some erasedPlan) :
    ∃ (plan : List CloseEntry) (raw : Footprint)
      (closingRequirements : Requirements (OwnerClosingSource.retirements plan))
      (requestRow resumeRow : Footprint),
      makePlan capture = some plan ∧
      DeclaredSourceClosing.PlanTemplate operations policy contracts tables world .none plan raw closingRequirements ∧
      requestRow ⊆ row ∧ resumeRow ⊆ row ∧
      (∃ (input answer : Value) (capDemand : List Nat) (capReq : Requirements capDemand) (capRecords store : Store),
        DeclaredSourceFrames.Segment operations policy contracts tables world capture input answer capDemand capReq capRecords ∧
        Checked store (OwnerPhases.ofStack tables tail)
          (OwnerPhaseTransitions.available (ownedTickets whole)) capReq resumeRow) ∧
      ∀ (_ : checkClosing (CallableProtectionFrames.contextOf tables tail) outside raw (requestRow ++ resumeRow) = true),
        ∃ (contract : Owners.Contract) (closingRow : Footprint) (after : Configuration)
          (nextDemand : List Nat) (nextRow : Footprint),
          (∃ argument, operations requested operation = some (argument, contract.input)) ∧
          contract.resumeRow = resumeRow ∧ contract.closeRow = some closingRow ∧
          residualize (CallableProtectionFrames.contextOf tables tail) raw = some closingRow ∧
          closingRow ⊆ requestRow ++ resumeRow ∧
          RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
          CheckedState operations policy (contracts.insert owner contract) tables world outside
            after.scope after.expression after.stack output nextDemand nextRow ∧
          nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
          ownedTickets after.stack = owner :: ownedTickets whole := by
  obtain ⟨input, argument, payloadAllowed, requirements, records, disposals, parameter, binder, body,
    offered, offeredRow, requestRow, pendingRow, operationKnown, payload, closed, pending, closing,
    pendingCheck, unique, clause, capabilities, found, mode, availableRow, exported, offeredAccepted,
    pendingAccepted, sameRow⟩ := DeclaredSourceRequests.request_parts source cut isValue
  obtain ⟨answer, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capRow, tailRow,
    annotation, selected, saved, surviving, sameDemand, sameRecords, splitRow, savedCheck, tailCheck⟩ :=
    RecursiveCapture.capture_segments_checked_with_frames cut pending pendingCheck
  have savedChecked : Checked (records ++ disposals) (OwnerPhases.ofStack tables tail)
      (OwnerPhaseTransitions.available (ownedTickets whole)) capReq capRow := by
    simpa only [List.append_nil] using savedCheck
  obtain ⟨plan, raw, closingRequirements, built, safe, internal, template, owners, unprotected⟩ :=
    DeclaredSourceClosing.checked_disposal_template saved disposal
  refine ⟨plan, raw, closingRequirements, requestRow, capRow, built, template, ?_, ?_,
    ⟨input, answer, capDemand, capReq, capRecords, records ++ disposals, saved, savedChecked⟩, ?_⟩
  · rw [sameRow]; exact List.subset_append_left _ _
  · rw [sameRow, splitRow]
    exact (List.subset_append_left _ _).trans (List.subset_append_right _ _)
  · intro admitted
    obtain ⟨checkedRow, checkedExport, checkedAccepted, checkedBudget⟩ :=
      DeclaredCallbackAdmission.check_closing_iff.mp admitted
    have closingAccepted := residual_admitted_iff.mpr ⟨checkedRow, checkedExport, checkedAccepted⟩
    obtain ⟨contract, allowed, clauseDemand, clauseRequirements, store, remainingDemand, remainingRow,
      closingRow, actualRequestRow, resumeSame, requestExport, inputSame, closeSame, closingExport, closingAllowed,
      balance, clauseSource, resumeCheck, disposeCheck, finish⟩ :=
      DeclaredSourceCapture.capture_from_declaration_split cut pending closing annotation selected saved surviving
        sameDemand sameRecords splitRow savedChecked tailCheck unique fresh clause capabilities operationKnown
        payload closed found availableRow offeredAccepted pendingAccepted built internal template (List.Subset.refl _) closingAccepted
    have requestSame := Option.some.inj (requestExport.symm.trans exported)
    subst actualRequestRow
    have closingSame := Option.some.inj (closingExport.symm.trans checkedExport)
    subst checkedRow
    obtain ⟨clauseRow, step, next, balanced, bounded, owned⟩ := finish (resumeSame.symm ▸ checkedBudget)
    exact ⟨contract, closingRow, _, _, _, ⟨argument, by simpa only [inputSame] using operationKnown⟩, resumeSame, closeSame, closingExport, checkedBudget, step, next,
      balanced, sameRow ▸ bounded, owned⟩

theorem prepare_checked_disposal
    (source : CheckedState operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (cut : HandlerCut requested whole capture tail handler)
    (isValue : operand.IsValue) (fresh : contracts owner = none)
    (disposal : ClosingAdmission.checkedDisposal capture.erase tail.erase = some erasedPlan) :
    ∃ (plan : List CloseEntry) (raw : Footprint)
      (closingRequirements : Requirements (OwnerClosingSource.retirements plan))
      (requestRow resumeRow : Footprint),
      makePlan capture = some plan ∧
      DeclaredSourceClosing.PlanTemplate operations policy contracts tables world .none plan raw closingRequirements ∧
      requestRow ⊆ row ∧ resumeRow ⊆ row ∧
      (∃ (input answer : Value) (capDemand : List Nat) (capReq : Requirements capDemand) (capRecords store : Store),
        DeclaredSourceFrames.Segment operations policy contracts tables world capture input answer capDemand capReq capRecords ∧
        Checked store (OwnerPhases.ofStack tables tail)
          (OwnerPhaseTransitions.available (ownedTickets whole)) capReq resumeRow) ∧
      ∀ (_ : checkClosing (CallableProtectionFrames.contextOf tables tail) outside raw (requestRow ++ resumeRow) = true),
        ∃ (contract : Owners.Contract) (closingRow : Footprint) (after : Configuration)
          (nextDemand : List Nat) (nextRow : Footprint),
          contract.resumeRow = resumeRow ∧ contract.closeRow = some closingRow ∧
          residualize (CallableProtectionFrames.contextOf tables tail) raw = some closingRow ∧
          closingRow ⊆ requestRow ++ resumeRow ∧
          RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
          CheckedState operations policy (contracts.insert owner contract) tables world outside
            after.scope after.expression after.stack output nextDemand nextRow ∧
          nextDemand.Perm (owner :: demand) ∧ nextRow ⊆ row ∧
          ownedTickets after.stack = owner :: ownedTickets whole := by
  obtain ⟨plan, raw, requirements, requestRow, resumeRow, built, template, requestBound, resumeBound, saved, finish⟩ :=
    prepare_checked_disposal_with_input source cut isValue fresh disposal
  refine ⟨plan, raw, requirements, requestRow, resumeRow, built, template, requestBound, resumeBound, saved, ?_⟩
  intro admitted
  obtain ⟨contract, closingRow, after, nextDemand, nextRow, inputKnown, rest⟩ := finish admitted
  exact ⟨contract, closingRow, after, nextDemand, nextRow, rest⟩

namespace Examples
open SourceCallableExamples (operations effect operation_known)
open DeclaredSources (Expression Offer Declarations)

def policy : Syntax.TicketPolicy := fun _ => ⟨false, true⟩
def contracts : Owners.Contracts := fun _ => none
def clauses : Clauses := .cons 0 1 9 (.discard 9) .nil
def table : List (Nat × ClauseContract) := [(0, ⟨true, some [], none⟩)]
def handler : HandlerData := ⟨104, effect, clauses, .none, .unit, rfl⟩
def tables : CallableProtectionFrames.Tables := fun _ => table
def whole : Stack := .push (.handler handler) .nil
def request : Code := .perform (Instantiation.freezeEffect effect) 0 .unit
def empty : Requirements [] := .request [] []

theorem declaration : Declarations operations policy contracts [] Environment.empty [] effect .unit clauses table := by
  have ordinary : Offer operations policy contracts [] Environment.empty [] 1 9 .unit .unit .unit [] []
      (.discard 9) false true (some []) := by
    apply Offer.available (fun _ => rfl) (fun _ => rfl)
    intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
    have known : (contracts.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
    have body : Expression operations policy (contracts.insert owner contract) [] [] (.ticket 9 owner)
        (Environment.empty.extend 1 .unit) (.discard 9) .unit (owner :: contract.closeDemand)
        (.invoke ⟨owner, .dispose⟩ contract.closeDemand []) :=
      .discard known rfl rfl heldSame (closeSame.symm ▸ List.Subset.refl [])
    exact .typed body ClauseRowAdmission.discard_rows
  exact .cons operation_known ordinary .unavailable .nil

theorem handler_typed : ScopedPorts.FrameTyped operations.ports contracts.ports.types [] (.handler handler) := by
  refine .handler (residual := []) ⟨.none, .none⟩
    (.cons (port_lookup operation_known) (.discard (List.Subset.refl [])) .nil) ?_ (by decide)
  intro operation input output known
  by_cases same : operation = 0
  · simp [same, handler, clauses, ScopedTyping.clauseKeys]
  · simp [Operations.ports, operations, same, handler] at known

theorem checked_request : CheckedState operations policy contracts tables [] [] .none request whole .unit [] [] := by
  have current : Expression operations policy contracts [] [effect] .none Environment.empty request .unit []
      (.emitAfter empty [] [⟨effect, 0, false⟩]) :=
    .perform operation_known List.mem_cons_self (.stable .unit)
      (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
  have pending : DeclaredSourceFrames.Segment operations policy contracts tables [] whole .unit .unit []
      (.sequence (empty.prepend []) empty) [] :=
    DeclaredSourceFrames.push (.handler (tables := tables) handler_typed rfl declaration
      (.cons (.discard rfl) .nil) (.cons (by decide) .nil)) .nil
  exact .checked (.checked current .none pending) (.push .nil) (by decide)
    (RecursiveRequirements.evaluate_sound (by
      simp only [empty, Requirements.prepend, RecursiveRequirements.evaluate, RecursiveRequirements.evaluateFuel]
      decide)) rfl

theorem disposal_enabled : (lookup 0 (tables handler)).map ClauseContract.dispose = some true ∧
    ClosingAdmission.checkedDisposal whole.erase Stack.nil.erase = some [] := by decide

/-- The budget is obtained before allocation. Empty closing is enough to
exercise an actually disposing clause and the complete checked capture path. -/
theorem checked_disposing_capture :
    ∃ (contract : Owners.Contract) (after : Configuration) (nextDemand : List Nat) (nextRow : Footprint),
      contract.resumeRow = [] ∧ contract.closeRow = some [] ∧
      RawStep ⟨request, .none, whole⟩ after [.ticket 20] [] ∧
      CheckedState operations policy (contracts.insert 20 contract) tables [] []
        after.scope after.expression after.stack .unit nextDemand nextRow ∧
      nextDemand.Perm [20] ∧ nextRow ⊆ [] ∧ ownedTickets after.stack = [20] := by
  have cut : HandlerCut effect whole whole .nil handler := .hit handler .nil rfl
  obtain ⟨plan, raw, closingRequirements, requestRow, resumeRow, built, template, requestBound, resumeBound,
    saved, finish⟩ := prepare_checked_disposal checked_request cut trivial (owner := 20) rfl disposal_enabled.2
  have planEmpty : plan = [] := by simpa [whole, makePlan] using built.symm
  subst plan
  cases template with
  | nil =>
    have requestEmpty : requestRow = [] := List.subset_nil.mp requestBound
    have resumeEmpty : resumeRow = [] := List.subset_nil.mp resumeBound
    subst requestRow; subst resumeRow
    obtain ⟨contract, closingRow, after, nextDemand, nextRow, resumeSame, closeSame, exported, budget,
      step, next, balanced, bounded, owners⟩ := finish (by decide)
    have closingEmpty : closingRow = [] := List.subset_nil.mp budget
    subst closingRow
    exact ⟨contract, after, nextDemand, nextRow, resumeSame, closeSame, step, next, balanced, bounded, owners⟩

end Examples

end Ash.OneShot.CheckedCaptureBudgets

#print axioms Ash.OneShot.CheckedCaptureBudgets.prepare_checked_disposal

#print axioms Ash.OneShot.CheckedCaptureBudgets.Examples.declaration

#print axioms Ash.OneShot.CheckedCaptureBudgets.Examples.handler_typed

#print axioms Ash.OneShot.CheckedCaptureBudgets.Examples.checked_request

#print axioms Ash.OneShot.CheckedCaptureBudgets.Examples.disposal_enabled

#print axioms Ash.OneShot.CheckedCaptureBudgets.Examples.checked_disposing_capture

#print axioms Ash.OneShot.CheckedCaptureBudgets.prepare_checked_disposal_with_input
