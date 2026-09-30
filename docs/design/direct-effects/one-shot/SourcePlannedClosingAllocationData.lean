import SourcePlannedClosingRecomposition

/-! Construct the stronger closing template from the retained joint source and
carry it at the exact raw footprint and requirement body used by allocation.
The certificate is source evidence; scheduling remains a separate judgment. -/
namespace Ash.OneShot.SourcePlannedClosingAllocationData
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Contracts)
open SourceContextualHints (Hints)
open SourcePlannedClosingPlans (Plans Template)
open SourcePlannedCheckedAllocationData (CaptureData)
open RecursiveRequirements (Requirements)
open OwnerClosingSource (retirements)
abbrev Receiving := SourceDependencyCapture.Scope

def Certificate (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (world : List Nat) (plan : List CloseEntry)
    (captured : Receiving) (raw : Footprint) (requirements : Requirements (retirements plan)) : Prop :=
  ∃ hints : Hints captured.forClosing, ∃ plans : Plans plan hints,
    Template operations policy contracts tables world .none plans raw requirements

/-- The actual saved source determines the callback annotations. Erasure
supplies the shared allocator with the same template, not another witness. -/
theorem capture_closing
    (source : CaptureData operations policy contracts tables families required actions outward world whole capture tail handler
      owner parameter binder code argument input output offered row records incoming outgoing
      oldAnswer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq)
    (built : makePlan capture = some plan) :
    ∃ raw, ∃ closingRequirements : Requirements (retirements plan),
      SourceDependencySchemes.Closing.Template operations.erase policy contracts.erase tables world .none
        plan raw closingRequirements capScope.forClosing ∧
      Certificate operations policy contracts tables world plan capScope raw closingRequirements := by
  cases source with
  | checked annotation scopeKnown saved waiting records resume close data =>
      obtain ⟨plans, contents⟩ := SourcePlannedClosingPlans.plan_contents saved built
      obtain ⟨raw, requirements, template⟩ := contents.template (tables := tables) (caller := .none)
      exact ⟨raw, requirements, template.erase, _, plans, template⟩

theorem Certificate.transport
    (certificate : Certificate operations policy contracts tables world plan captured raw requirements)
    (extension : contracts.Extends nextContracts) :
    Certificate operations policy nextContracts tables world plan captured raw requirements := by
  obtain ⟨hints, plans, template⟩ := certificate
  exact ⟨hints, plans, template.transport extension⟩

end Ash.OneShot.SourcePlannedClosingAllocationData

#print axioms Ash.OneShot.SourcePlannedClosingAllocationData.capture_closing
#print axioms Ash.OneShot.SourcePlannedClosingAllocationData.Certificate.transport
