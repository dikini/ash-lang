import SourceAnnotatedClosingRecomposition
import SourceAnnotatedClosingRecords
import SourceAnnotatedCaptureData

/-! The generic allocator carries annotated closing evidence at the existing
raw plan indices. Its witness retains the actual callback syntax and source;
erasure supplies the older certificate from that same witness. -/
namespace Ash.OneShot.SourceAnnotatedClosingData

variable [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy]
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Contracts)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest closingForest)
open SourceAnnotatedClosingPlans (Plans Template)
open SourceAnnotatedCaptureData (CaptureData)
open RecursiveRequirements (Requirements)
open OwnerClosingSource (retirements)

/-- Materialize the selected stored source at the actual caller and schedule.
The returned annotated stack erases to the machine's exact closing control. -/
theorem Certificate.materialize {hints : Hints captured} {saved : Forest hints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (certificate : Certificate operations policy contracts tables world capture plan saved raw requirements)
    (checked : SourceScheduledChecks.Pending outward actions phases world saved.forClosing outside)
    (typed : ScopedPorts.PlanTyped operations.erase.erase.ports world closing plan)
    (scope : ScopedPorts.EffectScopeKnown contracts.erase.erase.ports caller) :
    ∃ stack : SourceAnnotatedRuntime.Stack,
      stack.erase = closeControl caller plan ∧
      SourceAnnotatedRuntimeTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
        stack .unit .unit (retirements plan) requirements [] saved.forClosing outside
        (ScopedPorts.planProvides plan ++ closing) closing ∧
      ∃ annotated, SourceAnnotatedRuntime.makePlan capture = some annotated ∧
        stack = SourceAnnotatedRuntime.closeControl caller annotated := by
  cases certificate with
  | checked built template same =>
      rw [← same] at checked
      have source := (template.scope (second := caller)).scheduled_source
        (evidence := evidence) (families := families) (required := required) checked typed scope
      rw [same] at source
      exact ⟨_, SourceAnnotatedRuntime.closeControl_erase _ _, source, _, built, rfl⟩

/-- Allocation accepts the old machine's actual plan, recovers its annotated
origin, and extracts callback sources once from the captured typed segment. -/
theorem capture_closing
    (source : CaptureData (evidence := evidence) (currentEvidence := currentEvidence) operations policy contracts tables families required actions outward world whole capture tail handler
      owner parameter binder code argument input output offered row records incoming outgoing annotations savedEvidence
      oldAnswer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq)
    (built : makePlan capture.erase = some plan) :
    ∃ raw, ∃ closingRequirements : Requirements (retirements plan),
      SourceDependencySchemes.Closing.Template operations.erase policy contracts.erase tables world .none
        plan raw closingRequirements capScope.forClosing ∧
      CaptureData (evidence := evidence) (currentEvidence := currentEvidence) operations policy contracts tables families required actions outward world whole capture tail handler
        owner parameter binder code argument input output offered row records incoming outgoing annotations
        (fun saved => Certificate operations policy contracts tables world capture plan saved raw closingRequirements)
        oldAnswer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq := by
  obtain ⟨annotated, retained, erased⟩ := SourceAnnotatedRuntime.makePlan_of_raw capture built
  subst plan
  cases source with
  | checked annotation scopeKnown saved waiting records resume close data kept savedMatched waitingMatched clauseKept =>
      obtain ⟨plans, contents, same⟩ := SourceAnnotatedClosingPlans.plan_contents saved retained
      obtain ⟨raw, requirements, template⟩ := contents.template (tables := tables) (caller := .none)
      exact ⟨raw, requirements, template.erase.erase,
        .checked annotation scopeKnown saved waiting records resume close data (.checked retained template same) savedMatched waitingMatched clauseKept⟩

/-- Existing allocation accounting receives its certificate by projection;
the richer witness remains available for annotated disposal materialization. -/
theorem erase_capture_certificate
    (source : CaptureData (evidence := evidence) (currentEvidence := currentEvidence) operations policy contracts tables families required actions outward world whole capture tail handler
      owner parameter binder code argument input output offered row records incoming outgoing annotations
      (fun saved => Certificate operations policy contracts tables world capture plan saved raw closingRequirements)
      oldAnswer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq) :
    SourcePlannedClosingAllocationData.Certificate operations policy contracts tables world plan capScope raw closingRequirements := by
  cases source with
  | checked annotation scopeKnown saved waiting records resume close data kept savedMatched waitingMatched clauseKept => exact kept.erase.erase

end Ash.OneShot.SourceAnnotatedClosingData

#print axioms Ash.OneShot.SourceAnnotatedClosingData.capture_closing
#print axioms Ash.OneShot.SourceAnnotatedClosingData.erase_capture_certificate

#print axioms Ash.OneShot.SourceAnnotatedClosingData.Certificate.materialize

namespace Ash.OneShot.SourceAnnotatedClosingRecords
open ScopedExpressions ScopedExecution
open SourcePlannedTyping (Operations Contracts)
open SourceAnnotatedClosingData (Certificate)
open SourceScheduledSavedPlans (Saved Annotations Matches)
open SourceRetainedPlans (Forest)
open SourceContextualHints (Hints)
open OwnerClosingSource (retirements)

/-- Lookup returns the template at the exact forest selected by the active
owner cut, rather than another plan with equal erased dependencies. -/
theorem selected_template
    [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy]
    [SourceScheduledChecks.DeclarationProjection admission certification] {hints : Hints scope} {forest : Forest hints}
    {savedHints : Hints captured} {saved : Forest savedHints}
    (source : SourceAnnotatedRuntimeTyping.Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements resumes forest outside incoming outgoing)
    (closing : Records operations policy contracts tables annotations world stack disposals)
    (matched : Matches annotations forest)
    (cut : SourceScheduledNeutral.OwnerCut owner forest front saved tail)
    (looked : RecursiveRequirements.lookup ⟨owner, .dispose⟩ (resumes ++ disposals) = some body)
    (unique : (ownedTickets stack.erase).Nodup)
    (located : SourceAnnotatedRuntime.CapturedIn owner capture stack) :
    ∃ (plan : List CloseEntry) (raw : ProtectionContracts.Footprint)
      (requirements : RecursiveRequirements.Requirements (retirements plan)),
      makePlan capture.erase = some plan ∧ body = ⟨retirements plan, requirements⟩ ∧
      Certificate operations policy contracts tables world capture plan saved raw requirements := by
  rcases List.mem_append.mp (SourceTemplates.lookup_member looked) with resume | disposal
  · have impossible := RecursiveRecords.resume_mode source.erase.source.source.erase.erase.source.erase resume
    cases impossible
  · cases closing.member disposal with
    | dispose stored actual built recorded certificate =>
        cases SourceAnnotatedRuntime.captured_in_unique unique actual located
        have same := Option.some.inj (recorded.symm.trans (matched.selected cut))
        cases same
        exact ⟨_, _, _, built, rfl, certificate⟩

end Ash.OneShot.SourceAnnotatedClosingRecords

#print axioms Ash.OneShot.SourceAnnotatedClosingRecords.selected_template
