import CoreInitialExample

/-!
TASK-0032 / DN-0033 component evidence for the conditional
closing-separation field of clause Interface. Its physical capture constructors
derive the field from owner accounting and uniqueness. This is not a full Program. Resume-only
external demands remain unrestricted: separation below is required only when
actual disposal is permitted. Ownership and interpretation claims retain their
separate premises; no successor state or future execution is assumed.
-/
namespace Ash.OneShot.CoreClauseCoherence
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open OwnerPhaseTransitions (Phases spendAll)
open RecursiveRequirements (Requirements Store Checked)
open ClauseRowAdmission (Interface)

/-- Consuming owners absent from live receivers preserves their exact ordered
    interpretation, including held flags. Spent-name absence is unnecessary. -/
theorem project_spendAll_absent_live
    (separate : ∀ owner ∈ demand, owner ∉ OwnerPhaseTransitions.liveNames receiving) :
    OwnerPhaseTransitions.project receiving (spendAll before demand) =
      OwnerPhaseTransitions.project receiving before :=
  OwnerPhaseTransitions.project_spendAll_absent_live separate

theorem export_spendAll_absent_live
    (separate : ∀ owner ∈ demand, owner ∉ OwnerPhaseTransitions.liveNames receiving) :
    OwnerSource.exportAt receiving (spendAll before demand) raw =
      OwnerSource.exportAt receiving before raw := by
  unfold OwnerSource.exportAt
  rw [project_spendAll_absent_live separate]

/-- Physical capture ownership separates closing demand from active tail
    owners. This derives the finite condition from existing ownership evidence. -/
theorem owned_closing_demand_separate {closingDemand : List Nat} {capture tail : Stack}
    (accounting : closingDemand.Perm (ownedTickets capture))
    (unique : (ownedTickets (capture.append tail)).Nodup) :
    ∀ owner ∈ closingDemand, owner ∉ OwnerPhaseTransitions.liveNames
      (OwnerPhases.ofStack tables tail) :=
  OwnerPhaseTransitions.owned_closing_demand_separate accounting unique

/-- UnwindTemplate already proves the required physical owner accounting. -/
theorem unwind_closing_demand_separate
    (source : SourceDependencyFrames.UnwindTemplate operations policy contracts tables world
      capture demand requirements)
    (unique : (ownedTickets (capture.append tail)).Nodup) :
    ∀ owner ∈ demand, owner ∉ OwnerPhaseTransitions.liveNames
      (OwnerPhases.ofStack tables tail) :=
  owned_closing_demand_separate source.ownership unique

/-- The selected live boundary disappears; separated capture owners change no
    remaining interpretation in the receiving tail. -/
theorem export_after_selected_consumption
    (fresh : owner ∉ OwnerPhaseTransitions.liveNames tail)
    (separate : ∀ other ∈ demand, other ∉ OwnerPhaseTransitions.liveNames tail) :
    OwnerSource.exportAt (.live owner held :: tail) (spendAll before (owner :: demand)) raw =
      OwnerSource.exportAt tail before raw := by
  unfold OwnerSource.exportAt
  rw [OwnerPhaseTransitions.project_after_selected_consumption fresh separate]

/-- The interface field is conditional on disposal. Equal continuation
    demands transfer physical closing separation to the resume path. -/
theorem disposing_resume_demand_separate {contract : CoherentSourceTypes.Owners.Contract}
    (interface : Interface owner contract disposes store tail before requestRow)
    (permitted : disposes = true)
    (balance : contract.closeDemand.Perm contract.resumeDemand) :
    ∀ other ∈ contract.resumeDemand, other ∉ OwnerPhaseTransitions.liveNames tail := by
  intro other member
  exact interface.closingSeparate permitted other (balance.mem_iff.mpr member)

/-- Post-resume effectful work keeps its actual raw footprint. The supplied
    advertisement is interpreted at exactly the same tail and phase; no held
    bit is weakened and no wider coverage relation is introduced. -/
theorem disposing_resume_then_suffix_checked
    (interface : Interface owner contract disposes store tail before requestRow)
    (permitted : disposes = true)
    (balance : contract.closeDemand.Perm contract.resumeDemand)
    (exported : OwnerSource.exportAt tail before raw = some requestRow) :
    Checked store (.live owner contract.held :: tail) before
      (.sequence (.sequence (.request [] [])
        (.invoke ⟨owner, .resume⟩ contract.resumeDemand []))
        (.emitAfter (.request [] []) [] raw))
      (contract.resumeRow ++ requestRow) ∧
    EffectBounds.Covers (requestRow ++ contract.resumeRow) (contract.resumeRow ++ requestRow) :=
  interface.resume_then_suffix_checked permitted balance exported

/-- At a physical capture boundary the conditional premise is
    derived from closing ownership and uniqueness, rather than assumed of an
    arbitrary interface. The resume-only case gains no restriction. -/
theorem disposing_owned_capture_resume_then_suffix_checked
    {capture outside : Stack}
    (interface : Interface owner contract disposes store
      (OwnerPhases.ofStack tables outside) before requestRow)
    (permitted : disposes = true)
    (balance : contract.closeDemand.Perm contract.resumeDemand)
    (closingOwnership : contract.closeDemand.Perm (ownedTickets capture))
    (unique : (ownedTickets (capture.append outside)).Nodup)
    (exported : OwnerSource.exportAt (OwnerPhases.ofStack tables outside) before raw = some requestRow) :
    Checked store (.live owner contract.held :: OwnerPhases.ofStack tables outside) before
      (.sequence (.sequence (.request [] [])
        (.invoke ⟨owner, .resume⟩ contract.resumeDemand []))
        (.emitAfter (.request [] []) [] raw))
      (contract.resumeRow ++ requestRow) ∧
    EffectBounds.Covers (requestRow ++ contract.resumeRow) (contract.resumeRow ++ requestRow) :=
  disposing_resume_then_suffix_checked
    { interface with closingSeparate := fun _ => owned_closing_demand_separate closingOwnership unique }
    permitted balance exported

open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreInitialExample
  (writeRequirements)

/-- The kernel's concrete post-resume cell write uses the same raw demand and
    the same existing structural requirement, including its pure operand. -/
theorem disposing_resume_then_write_zero_checked
    (interface : Interface owner contract disposes store tail before requestRow)
    (permitted : disposes = true)
    (balance : contract.closeDemand.Perm contract.resumeDemand)
    (exported : OwnerSource.exportAt tail before [⟨.cell 0, 1, false⟩] = some requestRow) :
    Checked store (.live owner contract.held :: tail) before
      (.sequence (.sequence (.request [] [])
        (.invoke ⟨owner, .resume⟩ contract.resumeDemand [])) (writeRequirements 0))
      (contract.resumeRow ++ requestRow) ∧
    EffectBounds.Covers (requestRow ++ contract.resumeRow) (contract.resumeRow ++ requestRow) :=
  disposing_resume_then_suffix_checked interface permitted balance exported

/-- The earlier refutation's unprotected source capture and independently
    protected tail alias fail precisely this finite separation condition. -/
theorem prior_interface_witness_not_separated :
    ¬ (true = true → ∀ other ∈
      SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreInitialExample.InterfaceObstruction.selectedContract.closeDemand,
      other ∉ OwnerPhaseTransitions.liveNames
        SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreInitialExample.InterfaceObstruction.tail) := by
  intro separate
  have impossible := separate rfl 9 (by decide)
  exact impossible (by decide)

end Ash.OneShot.CoreClauseCoherence

#print axioms Ash.OneShot.CoreClauseCoherence.project_spendAll_absent_live
#print axioms Ash.OneShot.CoreClauseCoherence.export_spendAll_absent_live
#print axioms Ash.OneShot.CoreClauseCoherence.owned_closing_demand_separate
#print axioms Ash.OneShot.CoreClauseCoherence.unwind_closing_demand_separate
#print axioms Ash.OneShot.CoreClauseCoherence.disposing_resume_then_suffix_checked
#print axioms Ash.OneShot.CoreClauseCoherence.disposing_owned_capture_resume_then_suffix_checked
#print axioms Ash.OneShot.CoreClauseCoherence.disposing_resume_then_write_zero_checked
#print axioms Ash.OneShot.CoreClauseCoherence.prior_interface_witness_not_separated
