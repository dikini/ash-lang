import SourceScheduledCaptureData
import SourcePlannedClosingAllocationData

/-! Closing evidence retains the actual saved forest as an index. The shared
allocator carries it together with the typed capture, so rebuilding the live
source cannot choose a different forest with the same dependency annotations. -/
namespace Ash.OneShot.SourceScheduledClosingData
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Contracts)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest closingForest)
open SourcePlannedClosingPlans (Plans Template Checked)
open SourceScheduledCaptureData (CaptureData)
open RecursiveRequirements (Requirements)
open OwnerClosingSource (retirements)
abbrev Receiving := SourceDependencyCapture.Scope

def Certificate (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (world : List Nat) (plan : List CloseEntry)
    {captured : Receiving} {hints : Hints captured} (saved : Forest hints)
    (raw : Footprint) (requirements : Requirements (retirements plan)) : Prop :=
  ∃ plans : Plans plan (SourceContextualInvocationHints.forClosing hints),
    Template operations policy contracts tables world .none plans raw requirements ∧
    closingForest plans = saved.forClosing

theorem Certificate.erase {hints : Hints captured} {saved : Forest hints}
    (certificate : Certificate operations policy contracts tables world plan saved raw requirements) :
    SourcePlannedClosingAllocationData.Certificate operations policy contracts tables world plan captured raw requirements := by
  obtain ⟨plans, template, same⟩ := certificate
  exact ⟨_, plans, template⟩

theorem Certificate.transport
    (certificate : Certificate operations policy contracts tables world plan saved raw requirements)
    (extension : contracts.Extends nextContracts) :
    Certificate operations policy nextContracts tables world plan saved raw requirements := by
  obtain ⟨plans, template, same⟩ := certificate
  exact ⟨plans, template.transport extension, same⟩

/-- The existing dispose schedule checks the stored template itself. No new
template or equality inferred from erased dependency information is needed. -/
theorem Certificate.dispose_checked {hints : Hints scope} {forest : Forest hints}
    {selected : SourceContextualInvocationHints.Selection}
    {front : Forest selected.front} {saved : Forest selected.saved} {tail : Forest selected.tail}
    (certificate : Certificate operations policy contracts tables world plan saved raw requirements)
    (dispose : SourceScheduledChecks.Local outward actions phases world (.invoke (key := ⟨owner, .dispose⟩)) forest)
    (found : SourceContextualInvocationHints.findOwner owner hints = some selected)
    (same : HEq forest (front.append (.live (owner := owner) saved tail))) :
    ∃ plans : Plans plan (SourceContextualInvocationHints.forClosing selected.saved),
      Template operations policy contracts tables world .none plans raw requirements ∧
      closingForest plans = saved.forClosing ∧
      Checked outward actions (OwnerPhaseTransitions.spend phases owner) world
        (.running (selected.front.append (.spent (owner := owner) selected.tail))) plans := by
  obtain ⟨plans, template, retained⟩ := certificate
  refine ⟨plans, template, retained, ?_⟩
  have scheduled := dispose.dispose_schedule found same
  rw [← retained] at scheduled
  exact scheduled.closing_prefix_checked

/-- Extract the template once, and keep its forest equality in the same
constructor as the selected clause and both typed continuation pieces. -/
theorem capture_closing
    (source : CaptureData (evidence := evidence) operations policy contracts tables families required actions outward world whole capture tail handler
      owner parameter binder code argument input output offered row records incoming outgoing annotations savedEvidence
      oldAnswer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq)
    (built : makePlan capture = some plan) :
    ∃ raw, ∃ closingRequirements : Requirements (retirements plan),
      SourceDependencySchemes.Closing.Template operations.erase policy contracts.erase tables world .none
        plan raw closingRequirements capScope.forClosing ∧
      CaptureData (evidence := evidence) operations policy contracts tables families required actions outward world whole capture tail handler
        owner parameter binder code argument input output offered row records incoming outgoing annotations
        (fun saved => Certificate operations policy contracts tables world plan saved raw closingRequirements)
        oldAnswer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq := by
  cases source with
  | checked annotation scopeKnown saved waiting records resume close data kept savedMatched waitingMatched =>
      obtain ⟨plans, contents, same⟩ := SourceScheduledClosing.plan_contents saved built
      obtain ⟨raw, requirements, template⟩ := contents.template (tables := tables) (caller := .none)
      exact ⟨raw, requirements, template.erase,
        .checked annotation scopeKnown saved waiting records resume close data ⟨plans, template, same⟩ savedMatched waitingMatched⟩

/-- The legacy record view is a projection of the same capture certificate. -/
theorem erase_capture_certificate
    (source : CaptureData (evidence := evidence) operations policy contracts tables families required actions outward world whole capture tail handler
      owner parameter binder code argument input output offered row records incoming outgoing annotations
      (fun saved => Certificate operations policy contracts tables world plan saved raw closingRequirements)
      oldAnswer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq) :
    SourcePlannedClosingAllocationData.Certificate operations policy contracts tables world plan capScope raw closingRequirements := by
  cases source with
  | checked annotation scopeKnown saved waiting records resume close data kept savedMatched waitingMatched => exact kept.erase

end Ash.OneShot.SourceScheduledClosingData

#print axioms Ash.OneShot.SourceScheduledClosingData.Certificate.erase
#print axioms Ash.OneShot.SourceScheduledClosingData.Certificate.transport
#print axioms Ash.OneShot.SourceScheduledClosingData.Certificate.dispose_checked
#print axioms Ash.OneShot.SourceScheduledClosingData.capture_closing

#print axioms Ash.OneShot.SourceScheduledClosingData.erase_capture_certificate
