import SourceScheduledRecomposition

/-! Permission, phase and resource-world extension preserve the same retained
plans. Source registry transport reuses the existing expression and context
proofs; the old world-preserving entry points specialize the general transport. -/
namespace Ash.OneShot.SourceScheduledTransport
variable [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy]
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledChecks (Local Pending)
open SourceDependencySchemes (PhaseExtension)

/-- Every plan and receiving annotation remains the same. Available phases,
known permission entries and existing resource identities are retained. -/
theorem local_transport_world {plan : SourceDeclarationPlans.Plan dependencies} {hints : Hints scope} {forest : Forest hints}
    (source : Local outward actions before world plan forest)
    (extension : PhaseExtension before after) (permissions : Syntax.UsageExtension actions nextActions)
    (larger : world ⊆ nextWorld) :
    Local outward nextActions after nextWorld plan forest := by
  refine Local.rec
    (motive_1 := fun phases world _ _ _ plan hints _ => ∀ after nextActions nextWorld, PhaseExtension phases after →
      Syntax.UsageExtension actions nextActions → world ⊆ nextWorld → Local outward nextActions after nextWorld plan hints)
    (motive_2 := fun phases world _ _ _ _ forest outside _ => ∀ after nextActions nextWorld, PhaseExtension phases after →
      Syntax.UsageExtension actions nextActions → world ⊆ nextWorld → Pending outward nextActions after nextWorld forest outside)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (t := source) after nextActions nextWorld extension permissions larger
  · intros; exact .pure
  · intros
    rename_i guard scheduled ih after nextActions nextWorld extension permissions larger
    exact .request (SourceDependencySchemes.local_transport guard extension permissions larger)
      (fun captured tail saved waiting contract modes cut savedPlans waitingPlans same disposes =>
        ih captured tail saved waiting contract modes cut savedPlans waitingPlans same disposes after nextActions nextWorld extension permissions larger)
  · intros
    rename_i found access same restored ih after nextActions nextWorld extension permissions larger
    exact .resume found (SourcePlannedPhases.resume_transport access extension permissions) same
      (ih _ nextActions nextWorld extension.spend permissions larger)
  · intros
    rename_i found access same scheduled ih after nextActions nextWorld extension permissions larger
    exact .dispose found (SourcePlannedPhases.dispose_transport access extension permissions) same
      (ih _ nextActions nextWorld extension.spend permissions larger)
  · intros
    rename_i first second ihFirst ihSecond after nextActions nextWorld extension permissions larger
    exact .sequence (ihFirst after nextActions nextWorld extension permissions larger) (ihSecond after nextActions nextWorld extension permissions larger)
  · intros
    rename_i first second ihFirst ihSecond after nextActions nextWorld extension permissions larger
    exact .choice (ihFirst after nextActions nextWorld extension permissions larger) (ihSecond after nextActions nextWorld extension permissions larger)
  · intros
    rename_i recipes declarations supplied body ih after nextActions nextWorld extension permissions larger
    exact .handler recipes (SourcePlannedPhases.certified_clauses_world declarations larger) supplied
      (ih after nextActions nextWorld extension permissions larger)
  · intros
    rename_i body completion ihBody ihCompletion after nextActions nextWorld extension permissions larger
    exact .cleanup (ihBody after nextActions nextWorld extension permissions larger) (ihCompletion after nextActions nextWorld extension permissions larger)
  · intros
    rename_i body ih after nextActions nextWorld extension permissions larger
    exact .resource (fun identity fresh => ih identity (fun member => fresh (larger member)) after nextActions (nextWorld ++ [identity]) extension permissions
      (ScopedExpressions.append_subset larger (List.Subset.refl _)))
  · intros; exact .nil
  · intros
    rename_i code tail ihCode ihTail after nextActions nextWorld extension permissions larger
    exact .plain (ihCode after nextActions nextWorld extension permissions larger) (ihTail after nextActions nextWorld extension permissions larger)
  · intros
    rename_i supplied tail ih after nextActions nextWorld extension permissions larger
    exact .handler supplied (ih after nextActions nextWorld extension permissions larger)
  · intros
    rename_i tail ih after nextActions nextWorld extension permissions larger
    exact .cell (ih after nextActions nextWorld extension permissions larger)
  · intros
    rename_i completion tail ihCompletion ihTail after nextActions nextWorld extension permissions larger
    exact .cleanup (ihCompletion after nextActions nextWorld extension permissions larger) (ihTail after nextActions nextWorld extension permissions larger)
  · intros
    rename_i tail ih after nextActions nextWorld extension permissions larger
    exact .running (ih after nextActions nextWorld extension permissions larger)
  · intros
    rename_i saved tail ihSaved ihTail after nextActions nextWorld extension permissions larger
    exact .live (ihSaved after nextActions nextWorld extension permissions larger) (ihTail after nextActions nextWorld extension permissions larger)
  · intros
    rename_i tail ih after nextActions nextWorld extension permissions larger
    exact .spent (ih after nextActions nextWorld extension permissions larger)

theorem pending_transport_world {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (source : Pending outward actions before world forest outside)
    (extension : PhaseExtension before after) (permissions : Syntax.UsageExtension actions nextActions)
    (larger : world ⊆ nextWorld) :
    Pending outward nextActions after nextWorld forest outside := by
  induction forest generalizing outsideScope with
  | nil => exact .nil
  | plain plan rest ih => cases source with
    | plain code tail => exact .plain (local_transport_world code extension permissions larger) (ih tail)
  | handler rest ih => cases source with | handler supplied tail => exact .handler supplied (ih tail)
  | cell rest ih => cases source with | cell tail => exact .cell (ih tail)
  | cleanup plan rest ih => cases source with
    | cleanup completion tail => exact .cleanup (local_transport_world completion extension permissions larger) (ih tail)
  | running rest ih => cases source with | running tail => exact .running (ih tail)
  | live saved rest ihSaved ihRest => cases source with | live inside tail => exact .live (ihSaved inside) (ihRest tail)
  | spent rest ih => cases source with | spent tail => exact .spent (ih tail)

theorem local_transport {plan : SourceDeclarationPlans.Plan dependencies} {hints : Hints scope} {forest : Forest hints}
    (source : Local outward actions before world plan forest)
    (extension : PhaseExtension before after) (permissions : Syntax.UsageExtension actions nextActions) :
    Local outward nextActions after world plan forest :=
  local_transport_world source extension permissions (List.Subset.refl _)

theorem pending_transport {hints : Hints scope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (source : Pending outward actions before world forest outside)
    (extension : PhaseExtension before after) (permissions : Syntax.UsageExtension actions nextActions) :
    Pending outward nextActions after world forest outside :=
  pending_transport_world source extension permissions (List.Subset.refl _)

end Ash.OneShot.SourceScheduledTransport

namespace Ash.OneShot.SourceScheduledFrames
variable [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy]
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Contracts)
open SourcePlannedSources (expression_extension)
open SourcePlannedCheckedFrames (erased_extension context_extension declarations_extension)

theorem Frame.transport
    (frame : Frame (evidence := evidence) operations policy contracts tables families required outward actions before world
      receiving entry input output demand requirements layer decorate decoratePlans incoming outgoing)
    (extension : contracts.Extends nextContracts)
    (phases : SourceDependencySchemes.PhaseExtension before after)
    (permissions : Syntax.UsageExtension actions nextActions) :
    Frame (evidence := evidence) operations policy nextContracts tables families required outward nextActions after world
      receiving entry input output demand requirements layer decorate decoratePlans incoming outgoing := by
  have ports := CoherentSourceTypes.Owners.port_contracts_extension
    (SourceDependencyFrames.erased_contract_extension (erased_extension extension))
  have types := ScopedPorts.effect_extension_has_type_extension ports
  cases frame with
  | plain context scope inputAnnotation outputAnnotation checked =>
      exact .plain (context_extension context extension) (ScopedPorts.effect_scope_extension scope ports)
        inputAnnotation outputAnnotation (SourceScheduledTransport.local_transport checked phases permissions)
  | handler scope annotation clauses coverage unique declarations recipes supplied capabilities modes =>
      exact .handler (ScopedPorts.effect_scope_known_extension scope ports) annotation clauses coverage unique
        (declarations_extension declarations extension) recipes supplied capabilities modes
  | cell scope noEscape annotation interface =>
      exact .cell (ScopedPorts.scope_known_extension scope types) noEscape annotation (ScopedPorts.effect_frame_extension interface ports)
  | armed scope callback annotation interface checked =>
      exact .armed (ScopedPorts.scope_known_extension scope types) (expression_extension callback extension) annotation
        (ScopedPorts.effect_frame_extension interface ports) (SourceScheduledTransport.local_transport checked phases permissions)
  | running scope callback saved annotation interface =>
      exact .running (ScopedPorts.scope_known_extension scope types) (expression_extension callback extension)
        (expression_extension saved extension) annotation (ScopedPorts.effect_frame_extension interface ports)
  | closing scope interface =>
      exact .closing (ScopedPorts.scope_known_extension scope types) (ScopedPorts.effect_frame_extension interface ports)
  | retiring known interface => exact .retiring (extension _ _ known) (ScopedPorts.effect_frame_extension interface ports)

theorem Segment.transport
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward before world
      stack input output demand requirements records hints outside incoming outgoing)
    (extension : contracts.Extends nextContracts)
    (phases : SourceDependencySchemes.PhaseExtension before after)
    (permissions : Syntax.UsageExtension actions nextActions) :
    Segment (evidence := evidence) operations policy nextContracts tables families required nextActions outward after world
      stack input output demand requirements records hints outside incoming outgoing := by
  have ports := CoherentSourceTypes.Owners.port_contracts_extension
    (SourceDependencyFrames.erased_contract_extension (erased_extension extension))
  induction source with
  | nil bound => exact .nil bound
  | push head tail bound ih => exact .push (head.transport extension phases permissions) ih bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live (extension _ _ known) (permissions _ _ actionKnown) inputAnnotation answerAnnotation
        (ScopedPorts.effect_scope_known_extension scope ports) held ihSaved savedBound ihTail resume close bound
  | spent known annotation scope tail bound ih =>
      exact .spent (extension _ _ known) annotation (ScopedPorts.effect_scope_known_extension scope ports) ih bound

end Ash.OneShot.SourceScheduledFrames

#print axioms Ash.OneShot.SourceScheduledTransport.local_transport
#print axioms Ash.OneShot.SourceScheduledTransport.pending_transport
#print axioms Ash.OneShot.SourceScheduledFrames.Frame.transport
#print axioms Ash.OneShot.SourceScheduledFrames.Segment.transport

#print axioms Ash.OneShot.SourceScheduledTransport.local_transport_world
#print axioms Ash.OneShot.SourceScheduledTransport.pending_transport_world
