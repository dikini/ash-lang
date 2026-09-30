import SourceAnnotatedClosingData
import SourceAnnotatedStoredAllocationData

/-! Closing certificates are derived from the joint saved source without losing
its stored packets. Existing template and ownership proofs remain shared. -/
namespace Ash.OneShot.SourceAnnotatedStoredClosingData

variable [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy]
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Contracts)
open SourceAnnotatedStoredAllocationData (CaptureData)
open SourceAnnotatedClosingData (Certificate)
open RecursiveRequirements (Requirements)
open OwnerClosingSource (retirements)

/-- Allocation accepts the old machine's actual plan, recovers its annotated
origin, and extracts callback sources once from the captured typed segment. -/
theorem capture_closing
    (source : CaptureData (evidence := evidence) (currentEvidence := currentEvidence) operations policy contracts tables families required actions outward world whole capture tail handler
      owner parameter binder code argument input output offered row records incoming outgoing annotations savedEvidence savedStored waitingStored
      oldAnswer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq)
    (built : makePlan capture.erase = some plan) :
    ∃ raw, ∃ closingRequirements : Requirements (retirements plan),
      SourceDependencySchemes.Closing.Template operations.erase policy contracts.erase tables world .none
        plan raw closingRequirements capScope.forClosing ∧
      CaptureData (evidence := evidence) (currentEvidence := currentEvidence) operations policy contracts tables families required actions outward world whole capture tail handler
        owner parameter binder code argument input output offered row records incoming outgoing annotations
        (fun saved => Certificate operations policy contracts tables world capture plan saved raw closingRequirements) savedStored waitingStored
        oldAnswer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq := by
  obtain ⟨annotated, retained, erased⟩ := SourceAnnotatedRuntime.makePlan_of_raw capture built
  subst plan
  cases source with
  | checked annotation scopeKnown saved waiting records resume close data kept savedMatched waitingMatched clauseKept =>
      obtain ⟨plans, contents, same⟩ := SourceAnnotatedClosingPlans.plan_contents saved.forget retained
      obtain ⟨raw, requirements, template⟩ := contents.template (tables := tables) (caller := .none)
      exact ⟨raw, requirements, template.erase.erase,
        .checked annotation scopeKnown saved waiting records resume close data (.checked retained template same) savedMatched waitingMatched clauseKept⟩

/-- Existing allocation accounting receives its certificate by projection;
the richer witness remains available for annotated disposal materialization. -/
theorem erase_capture_certificate
    (source : CaptureData (evidence := evidence) (currentEvidence := currentEvidence) operations policy contracts tables families required actions outward world whole capture tail handler
      owner parameter binder code argument input output offered row records incoming outgoing annotations
      (fun saved => Certificate operations policy contracts tables world capture plan saved raw closingRequirements) savedStored waitingStored
      oldAnswer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq) :
    SourcePlannedClosingAllocationData.Certificate operations policy contracts tables world plan capScope raw closingRequirements := by
  cases source with
  | checked annotation scopeKnown saved waiting records resume close data kept savedMatched waitingMatched clauseKept => exact kept.erase.erase

end Ash.OneShot.SourceAnnotatedStoredClosingData

#print axioms Ash.OneShot.SourceAnnotatedStoredClosingData.capture_closing
#print axioms Ash.OneShot.SourceAnnotatedStoredClosingData.erase_capture_certificate
