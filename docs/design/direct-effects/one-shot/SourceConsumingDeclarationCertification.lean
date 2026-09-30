import SourceConsumingDeclarationEntry
import SourceDeclarationPolicyTransport

/-! Source-only declaration certification for consuming clauses. The proofs
inspect the existing syntax derivations; they use no receiving forest, owner
phase, successful capture or future scheduling premise. -/
namespace Ash.OneShot.SourceScheduledSourceInterfaces
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (Signature signature)
open SourcePlannedChecks (Certified)

/-- Authenticate actual nested clause plans through the existing stable-signature
transport, without asking whether the surrounding computation can execute. -/
theorem Declared.certified_signature {checking : Signature dependencies}
    (declared : Declared world checking) {plan : Plan dependencies}
    (same : signature plan = checking) : Certified outward world plan := by
  induction declared with
  | pure => cases plan; exact .pure
  | request => cases plan; exact .request
  | invoke => cases plan; exact .invoke
  | sequence left right ihLeft ihRight => cases plan with
    | sequence first second =>
        obtain ⟨firstSame, secondSame⟩ := Signature.sequence.inj same
        exact .sequence (ihLeft firstSame) (ihRight secondSame)
  | choice left right ihLeft ihRight => cases plan with
    | choice first second =>
        obtain ⟨firstSame, secondSame⟩ := Signature.choice.inj same
        exact .choice (ihLeft firstSame) (ihRight secondSame)
  | handler declarations body ih => cases plan with
    | handler required actual code =>
        obtain ⟨rfl, declarationsSame, bodySame⟩ := Signature.handler.inj same
        have recipes := declarations.signature_congr declarationsSame.symm
        exact .handler recipes.erase recipes.certified (ih bodySame)
  | cleanup callback body ihCallback ihBody => cases plan with
    | cleanup actualCallback actualBody =>
        obtain ⟨callbackSame, bodySame⟩ := Signature.cleanup.inj same
        exact .cleanup (ihCallback callbackSame) (ihBody bodySame)
  | resource body ih => cases plan with
    | resource actual =>
        exact .resource (fun identity fresh =>
          ih identity fresh (congrFun (Signature.resource.inj same) identity))

theorem Declared.certified {plan : Plan dependencies}
    (declared : Declared world (signature plan)) : Certified outward world plan :=
  declared.certified_signature rfl

end Ash.OneShot.SourceScheduledSourceInterfaces

namespace Ash.OneShot.SourceConsumingClauseAnnotations
open SourceDeclarationPlans (Plan ModePlans ClausePlans)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy DeclarationLaws)
open SourcePlannedChecks (Certified CertifiedModes CertifiedClauses)

variable [nested : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

/-- The existing consuming syntax supplies declaration certification independently
of its continuation bounds and their receiving-context checks. -/
theorem Body.certified (laws : DeclarationLaws nested admission certification outward)
    {plan : Plan dependencies} (body : Body world owner plan) :
    Certified (evidence := certification) outward world plan := by
  induction body with
  | resume => exact .invoke
  | dispose => exact .invoke
  | sequence required footprint declared rest ih =>
      exact .sequence
        ((SourceDeclarationPolicyTransport.certified_all SourcePlannedChecks.contextualPolicy certification outward
          (fun checked => laws.legacyCertification checked)).1 _ _ declared.certified) ih
  | choice first second ihFirst ihSecond => exact .choice ihFirst ihSecond
  | handler bounds admitted body ih =>
      exact .handler (laws.projected (laws.admitted admitted)) (laws.certified admitted) ih
  | cleanup required footprint declared body ih =>
      exact .cleanup
        ((SourceDeclarationPolicyTransport.certified_all SourcePlannedChecks.contextualPolicy certification outward
          (fun checked => laws.legacyCertification checked)).1 _ _ declared.certified) ih
  | resource body ih => exact .resource ih

theorem Modes.certified (laws : DeclarationLaws nested admission certification outward)
    {plans : ModePlans family} (modes : Modes world plans) :
    CertifiedModes (evidence := certification) outward world plans := by
  cases modes with
  | unavailable => exact .unavailable
  | available bodies => exact .available (fun owner => (bodies owner).certified laws)

theorem Declarations.certified (laws : DeclarationLaws nested admission certification outward)
    {plans : ClausePlans clauses families} (declarations : Declarations world plans) :
    CertifiedClauses (evidence := certification) outward world plans := by
  induction declarations with
  | nil => exact .nil
  | cons ordinary protectedMode rest ih =>
      exact .cons (ordinary.certified laws) (protectedMode.certified laws) ih

end Ash.OneShot.SourceConsumingClauseAnnotations

#print axioms Ash.OneShot.SourceScheduledSourceInterfaces.Declared.certified_signature
#print axioms Ash.OneShot.SourceScheduledSourceInterfaces.Declared.certified
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.certified
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Modes.certified
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Declarations.certified
