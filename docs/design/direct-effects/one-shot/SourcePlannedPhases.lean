import SourcePlannedNeutralChecks

/-! Permission, phase and resource-world extension for the stronger structural
source checks. Reuse the established extension relations and spend law. Fresh
allocation adds identities without reviving a consumed continuation. -/
namespace Ash.OneShot.SourcePlannedPhases
open SourceContextualHints (Hints)
open SourcePlannedChecks (Local Pending)
open SourceDependencySchemes (PhaseExtension)

private theorem resume_access (source : SourceDependencyCapture.ResumeChecked actions before owner scope result)
    (extension : PhaseExtension before after) (permissions : Syntax.UsageExtension actions nextActions) :
    SourceDependencyCapture.ResumeChecked nextActions after owner scope result := by
  cases source with
  | checked located known permission available => exact .checked located (permissions _ _ known) permission (extension _ available)

private theorem dispose_access (source : SourceDependencyCapture.DisposeChecked outward actions before owner scope result)
    (extension : PhaseExtension before after) (permissions : Syntax.UsageExtension actions nextActions) :
    SourceDependencyCapture.DisposeChecked outward nextActions after owner scope result := by
  cases source with
  | checked located known permission available unprotected closing =>
      exact .checked located (permissions _ _ known) permission (extension _ available) unprotected closing

/-- The existing contextual access witness transports independently of the
computation plan and its scheduling representation. -/
theorem resume_transport {hints : Hints scope}
    (source : SourceContextualInvocations.Resume actions before owner hints result)
    (extension : PhaseExtension before after) (permissions : Syntax.UsageExtension actions nextActions) :
    SourceContextualInvocations.Resume nextActions after owner hints result := by
  cases source with
  | checked found access compatible => exact .checked found (resume_access access extension permissions) compatible

theorem dispose_transport {hints : Hints scope}
    (source : SourceContextualInvocations.Dispose outward actions before owner hints result)
    (extension : PhaseExtension before after) (permissions : Syntax.UsageExtension actions nextActions) :
    SourceContextualInvocations.Dispose outward nextActions after owner hints result := by
  cases source with
  | checked found access compatible => exact .checked found (dispose_access access extension permissions) compatible

/-- A larger resource world retains every nested declaration witness. -/
theorem certified_clauses_world [evidence : SourcePlannedChecks.DeclarationPolicy] {plans : SourceDeclarationPlans.ClausePlans clauses families}
    (checked : SourcePlannedChecks.CertifiedClauses outward world plans) (larger : world ⊆ nextWorld) :
    SourcePlannedChecks.CertifiedClauses outward nextWorld plans := by
  refine SourcePlannedChecks.CertifiedClauses.rec
    (motive_1 := fun world _ plan _ => ∀ nextWorld, world ⊆ nextWorld → SourcePlannedChecks.Certified outward nextWorld plan)
    (motive_2 := fun world _ plan _ => ∀ nextWorld, world ⊆ nextWorld → SourcePlannedChecks.CertifiedModes outward nextWorld plan)
    (motive_3 := fun world _ _ plan _ => ∀ nextWorld, world ⊆ nextWorld → SourcePlannedChecks.CertifiedClauses outward nextWorld plan)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (t := checked) nextWorld larger
  · intros; exact .pure
  · intros; exact .request
  · intros; exact .invoke
  · intros; rename_i left right ihLeft ihRight nextWorld larger
    exact .sequence (ihLeft _ larger) (ihRight _ larger)
  · intros; rename_i left right ihLeft ihRight nextWorld larger
    exact .choice (ihLeft _ larger) (ihRight _ larger)
  · intros; rename_i recipes declarations body ihDeclarations ihBody nextWorld larger
    exact .handler recipes (ihDeclarations _ larger) (ihBody _ larger)
  · intros; rename_i callback body ihCallback ihBody nextWorld larger
    exact .cleanup (ihCallback _ larger) (ihBody _ larger)
  · intros; rename_i body ih nextWorld larger
    exact .resource (fun identity fresh => ih identity (fun member => fresh (larger member)) _
      (ScopedExpressions.append_subset larger (List.Subset.refl _)))
  · intros; exact .unavailable
  · intros; rename_i body ih nextWorld larger
    exact .available (fun owner => ih owner _ larger)
  · intros; exact .nil
  · intros; rename_i ordinary protectedMode rest ihOrdinary ihProtected ihRest nextWorld larger
    exact .cons (ihOrdinary _ larger) (ihProtected _ larger) (ihRest _ larger)

/-- Every plan and receiving annotation remains the same. Existing
available phases, known permissions and resource identities are retained. -/
theorem local_transport_world [certification : SourcePlannedChecks.DeclarationPolicy] {plan : SourceDeclarationPlans.Plan dependencies} {hints : Hints scope}
    (source : Local outward actions before world plan hints)
    (extension : PhaseExtension before after) (permissions : Syntax.UsageExtension actions nextActions) (larger : world ⊆ nextWorld) :
    Local outward nextActions after nextWorld plan hints := by
  refine Local.rec
    (motive_1 := fun phases world _ _ plan hints _ => ∀ after nextActions nextWorld, PhaseExtension phases after →
      Syntax.UsageExtension actions nextActions → world ⊆ nextWorld → Local outward nextActions after nextWorld plan hints)
    (motive_2 := fun phases world _ _ hints outside _ => ∀ after nextActions nextWorld, PhaseExtension phases after →
      Syntax.UsageExtension actions nextActions → world ⊆ nextWorld → Pending outward nextActions after nextWorld hints outside)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (t := source) after nextActions nextWorld extension permissions larger
  · intros; exact .pure
  · intros
    rename_i scope hints effect operation guard scheduled ih after nextActions nextWorld extension permissions larger
    exact .request (SourceDependencySchemes.local_transport guard extension permissions larger)
      (fun captured tail saved waiting contract modes same found disposes =>
        ih captured tail saved waiting contract modes same found disposes after nextActions nextWorld extension permissions larger)
  · intros
    rename_i owner hints result access restored ih after nextActions nextWorld extension permissions larger
    cases access with
    | checked found checked compatible =>
        exact .resume (.checked found (resume_access checked extension permissions) compatible)
          (ih _ nextActions nextWorld extension.spend permissions larger)
  · intros
    rename_i owner hints result access scheduled ih after nextActions nextWorld extension permissions larger
    cases access with
    | checked found checked compatible =>
        exact .dispose (.checked found (dispose_access checked extension permissions) compatible)
          (ih _ nextActions nextWorld extension.spend permissions larger)
  · intros
    rename_i first second ihFirst ihSecond after nextActions nextWorld extension permissions larger
    exact .sequence (ihFirst after nextActions nextWorld extension permissions larger) (ihSecond after nextActions nextWorld extension permissions larger)
  · intros
    rename_i first second ihFirst ihSecond after nextActions nextWorld extension permissions larger
    exact .choice (ihFirst after nextActions nextWorld extension permissions larger) (ihSecond after nextActions nextWorld extension permissions larger)
  · intros
    rename_i recipes declarations supplied body ih after nextActions nextWorld extension permissions larger
    exact .handler recipes (certified_clauses_world declarations larger) supplied (ih after nextActions nextWorld extension permissions larger)
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
    rename_i tail ih after nextActions nextWorld extension permissions larger
    exact .handler (ih after nextActions nextWorld extension permissions larger)
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

theorem pending_transport_world [certification : SourcePlannedChecks.DeclarationPolicy] {hints : Hints scope} {outside : Hints outsideScope}
    (source : Pending outward actions before world hints outside)
    (extension : PhaseExtension before after) (permissions : Syntax.UsageExtension actions nextActions) (larger : world ⊆ nextWorld) :
    Pending outward nextActions after nextWorld hints outside := by
  induction hints generalizing outsideScope with
  | nil => exact .nil
  | plain rest ih => cases source with
    | plain code tail => exact .plain (local_transport_world code extension permissions larger) (ih tail)
  | handler required rest ih => cases source with | handler tail => exact .handler (ih tail)
  | cell rest ih => cases source with | cell tail => exact .cell (ih tail)
  | cleanup rest ih => cases source with
    | cleanup completion tail => exact .cleanup (local_transport_world completion extension permissions larger) (ih tail)
  | running rest ih => cases source with | running tail => exact .running (ih tail)
  | live saved rest ihSaved ihRest => cases source with | live inside tail => exact .live (ihSaved inside) (ihRest tail)
  | spent rest ih => cases source with | spent tail => exact .spent (ih tail)


theorem local_transport [certification : SourcePlannedChecks.DeclarationPolicy] {plan : SourceDeclarationPlans.Plan dependencies} {hints : Hints scope}
    (source : Local outward actions before world plan hints)
    (extension : PhaseExtension before after) (permissions : Syntax.UsageExtension actions nextActions) :
    Local outward nextActions after world plan hints :=
  local_transport_world source extension permissions (List.Subset.refl _)

theorem pending_transport [certification : SourcePlannedChecks.DeclarationPolicy] {hints : Hints scope} {outside : Hints outsideScope}
    (source : Pending outward actions before world hints outside)
    (extension : PhaseExtension before after) (permissions : Syntax.UsageExtension actions nextActions) :
    Pending outward nextActions after world hints outside :=
  pending_transport_world source extension permissions (List.Subset.refl _)

end Ash.OneShot.SourcePlannedPhases

#print axioms Ash.OneShot.SourcePlannedPhases.local_transport
#print axioms Ash.OneShot.SourcePlannedPhases.pending_transport

#print axioms Ash.OneShot.SourcePlannedPhases.resume_transport
#print axioms Ash.OneShot.SourcePlannedPhases.dispose_transport

#print axioms Ash.OneShot.SourcePlannedPhases.certified_clauses_world

#print axioms Ash.OneShot.SourcePlannedPhases.local_transport_world

#print axioms Ash.OneShot.SourcePlannedPhases.pending_transport_world
