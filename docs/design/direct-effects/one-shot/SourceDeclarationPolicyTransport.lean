import SourceScheduledChecks

/-! Change declaration evidence on the same source syntax and actual retained
forests. Only pointwise implications between declaration judgments are needed;
permissions, phases, cuts and scheduling premises remain unchanged. -/
namespace Ash.OneShot.SourceDeclarationPolicyTransport
open ScopedExpressions
open SourceDeclarationPlans (Plan ClausePlans ModePlans)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

theorem certified_all (source target : SourcePlannedChecks.DeclarationPolicy) (outward : List Instance)
    (translate : ∀ {clauses families required} {plans : ClausePlans clauses families},
      source.accepts outward required plans → target.accepts outward required plans) :
    (∀ world {dependencies} (plan : Plan dependencies),
      SourcePlannedChecks.Certified (evidence := source) outward world plan →
      SourcePlannedChecks.Certified (evidence := target) outward world plan) ∧
    (∀ world {family} (plans : ModePlans family),
      SourcePlannedChecks.CertifiedModes (evidence := source) outward world plans →
      SourcePlannedChecks.CertifiedModes (evidence := target) outward world plans) ∧
    (∀ world {clauses families} (plans : ClausePlans clauses families),
      SourcePlannedChecks.CertifiedClauses (evidence := source) outward world plans →
      SourcePlannedChecks.CertifiedClauses (evidence := target) outward world plans) := by
  refine ⟨?_, ?_, ?_⟩
  all_goals first
    | (intro world dependencies plan checked
       apply SourcePlannedChecks.Certified.rec (evidence := source)
         (motive_1 := fun world {dependencies} plan _ =>
           SourcePlannedChecks.Certified (evidence := target) outward world plan)
         (motive_2 := fun world {family} plans _ =>
           SourcePlannedChecks.CertifiedModes (evidence := target) outward world plans)
         (motive_3 := fun world {clauses families} plans _ =>
           SourcePlannedChecks.CertifiedClauses (evidence := target) outward world plans) (t := checked))
    | (intro world family plans checked
       apply SourcePlannedChecks.CertifiedModes.rec (evidence := source)
         (motive_1 := fun world {dependencies} plan _ =>
           SourcePlannedChecks.Certified (evidence := target) outward world plan)
         (motive_2 := fun world {family} plans _ =>
           SourcePlannedChecks.CertifiedModes (evidence := target) outward world plans)
         (motive_3 := fun world {clauses families} plans _ =>
           SourcePlannedChecks.CertifiedClauses (evidence := target) outward world plans) (t := checked))
    | (intro world clauses families plans checked
       apply SourcePlannedChecks.CertifiedClauses.rec (evidence := source)
         (motive_1 := fun world {dependencies} plan _ =>
           SourcePlannedChecks.Certified (evidence := target) outward world plan)
         (motive_2 := fun world {family} plans _ =>
           SourcePlannedChecks.CertifiedModes (evidence := target) outward world plans)
         (motive_3 := fun world {clauses families} plans _ =>
           SourcePlannedChecks.CertifiedClauses (evidence := target) outward world plans) (t := checked))
  all_goals intros
  all_goals first
    | exact .pure
    | exact .request
    | exact .invoke
    | exact .sequence ‹_› ‹_›
    | exact .choice ‹_› ‹_›
    | exact .handler (translate ‹_›) ‹_› ‹_›
    | exact .cleanup ‹_› ‹_›
    | exact .resource ‹_›
    | exact .unavailable
    | exact .available ‹_›
    | exact .nil
    | exact .cons ‹_› ‹_› ‹_›

theorem certified_clauses {source target : SourcePlannedChecks.DeclarationPolicy}
    (translate : ∀ {clauses families required} {plans : ClausePlans clauses families},
      source.accepts outward required plans → target.accepts outward required plans)
    {plans : ClausePlans clauses families}
    (checked : SourcePlannedChecks.CertifiedClauses (evidence := source) outward world plans) :
    SourcePlannedChecks.CertifiedClauses (evidence := target) outward world plans :=
  (certified_all source target outward translate).2.2 world plans checked

theorem scheduled_all (source target : SourceScheduledChecks.DeclarationPolicy)
    (sourceCertification targetCertification : SourcePlannedChecks.DeclarationPolicy)
    (outward : List Instance) (actions : Syntax.UsageTickets)
    (admission : ∀ {clauses families required} {plans : ClausePlans clauses families},
      source.accepts outward required plans → target.accepts outward required plans)
    (certification : ∀ {clauses families required} {plans : ClausePlans clauses families},
      sourceCertification.accepts outward required plans → targetCertification.accepts outward required plans) :
    (∀ phases world {dependencies scope} {hints : Hints scope} (plan : Plan dependencies) (forest : Forest hints),
      SourceScheduledChecks.Local (admission := source) (certification := sourceCertification)
        outward actions phases world plan forest →
      SourceScheduledChecks.Local (admission := target) (certification := targetCertification)
        outward actions phases world plan forest) ∧
    (∀ phases world {scope outsideScope} {hints : Hints scope} {outsideHints : Hints outsideScope}
      (forest : Forest hints) (outside : Forest outsideHints),
      SourceScheduledChecks.Pending (admission := source) (certification := sourceCertification)
        outward actions phases world forest outside →
      SourceScheduledChecks.Pending (admission := target) (certification := targetCertification)
        outward actions phases world forest outside) := by
  constructor
  all_goals first
    | (intro phases world dependencies scope hints plan forest checked
       apply SourceScheduledChecks.Local.rec (admission := source) (certification := sourceCertification)
         (motive_1 := fun phases world {dependencies scope hints} plan forest _ =>
           SourceScheduledChecks.Local (admission := target) (certification := targetCertification)
             outward actions phases world plan forest)
         (motive_2 := fun phases world {scope outsideScope hints outsideHints} forest outside _ =>
           SourceScheduledChecks.Pending (admission := target) (certification := targetCertification)
             outward actions phases world forest outside) (t := checked))
    | (intro phases world scope outsideScope hints outsideHints forest outside checked
       apply SourceScheduledChecks.Pending.rec (admission := source) (certification := sourceCertification)
         (motive_1 := fun phases world {dependencies scope hints} plan forest _ =>
           SourceScheduledChecks.Local (admission := target) (certification := targetCertification)
             outward actions phases world plan forest)
         (motive_2 := fun phases world {scope outsideScope hints outsideHints} forest outside _ =>
           SourceScheduledChecks.Pending (admission := target) (certification := targetCertification)
             outward actions phases world forest outside) (t := checked))
  all_goals intros
  all_goals first
    | exact .pure
    | exact .nil
    | exact .request ‹_› ‹_›
    | exact .resume ‹_› ‹_› ‹_› ‹_›
    | exact .dispose ‹_› ‹_› ‹_› ‹_›
    | exact .sequence ‹_› ‹_›
    | exact .choice ‹_› ‹_›
    | exact .handler (admission ‹_›) (certified_clauses certification ‹_›) ‹_› ‹_›
    | exact .handler ‹_› ‹_›
    | exact .cleanup ‹_› ‹_›
    | exact .resource ‹_›
    | exact .plain ‹_› ‹_›
    | exact .cell ‹_›
    | exact .running ‹_›
    | exact .live ‹_› ‹_›
    | exact .spent ‹_›

end Ash.OneShot.SourceDeclarationPolicyTransport

#print axioms Ash.OneShot.SourceDeclarationPolicyTransport.certified_all
#print axioms Ash.OneShot.SourceDeclarationPolicyTransport.certified_clauses
#print axioms Ash.OneShot.SourceDeclarationPolicyTransport.scheduled_all
