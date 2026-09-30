import SourceConsumingDeclarationCertification

/-! Concrete declaration policies generated from existing structural consuming
judgments. The index counts layers of declaration evidence, not runtime handler
order or computation models. Every layer keeps inherited evidence and admits
explicitly bounded consuming declarations over the preceding layer. -/
namespace Ash.OneShot.SourceConsumingDeclarationPolicies
open SourceDeclarationPlans (ClausePlans)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy DeclarationLaws)

/-- An empty-world source derivation can be weakened to the actual resource
world. Bounds and nested declarations are checked before any capture is known. -/
def bounded (nested : DeclarationPolicy) : SourcePlannedFrames.DeclarationEvidence :=
  @SourceConsumingDeclarationEntry.evidence nested []

@[instance_reducible] def extendCapability (nested : DeclarationPolicy) : DeclarationPolicy where
  accepts := fun required {_ _} plans =>
    SourcePlannedRecipeDeclarations.Declarations required plans ∨
      nested.accepts required plans ∨ bounded nested required plans

@[instance_reducible] def extendAdmission (nested : DeclarationPolicy) : SourceScheduledChecks.DeclarationPolicy where
  accepts := fun _outward required {_ _} plans => (extendCapability nested).accepts required plans

@[instance_reducible] def extendCertification (nested : DeclarationPolicy)
    (previous : SourcePlannedChecks.DeclarationPolicy) : SourcePlannedChecks.DeclarationPolicy where
  accepts := fun outward required {clauses families} plans =>
    SourceContextualRequirements.DeclarationRecipes outward clauses families required ∨
      previous.accepts outward required plans ∨ bounded nested required plans

/-- Extend the static policy laws using the source derivation's certification.
No Local/Pending judgment, receiving scope, or future clause check is a premise. -/
theorem extend_laws {nested : DeclarationPolicy}
    {previousAdmission : SourceScheduledChecks.DeclarationPolicy}
    {previousCertification : SourcePlannedChecks.DeclarationPolicy}
    (laws : DeclarationLaws nested previousAdmission previousCertification outward) :
    DeclarationLaws (extendCapability nested) (extendAdmission nested)
      (extendCertification nested previousCertification) outward := by
  refine ⟨(fun checked => checked), ?_, ?_, (fun checked => Or.inl checked), (fun checked => Or.inl checked)⟩
  · intro world clauses families required plans checked
    rcases checked with recipes | inherited | structural
    · exact SourceDeclarationPolicyTransport.certified_clauses
        (source := SourcePlannedChecks.contextualPolicy)
        (fun old => Or.inl old) recipes.certified
    · exact SourceDeclarationPolicyTransport.certified_clauses
        (source := previousCertification)
        (fun old => Or.inr (Or.inl old)) (laws.certified inherited)
    · obtain ⟨bounds, annotation, admitted⟩ := structural
      exact SourceDeclarationPolicyTransport.certified_clauses
        (source := previousCertification)
        (fun old => Or.inr (Or.inl old))
        ((annotation.world_weaken (List.nil_subset world)).certified laws)
  · intro clauses families required plans checked
    rcases checked with recipes | inherited | structural
    · exact Or.inl recipes.erase
    · exact Or.inr (Or.inl (laws.projected (laws.admitted inherited)))
    · exact Or.inr (Or.inr structural)

@[instance_reducible] def capability : Nat → DeclarationPolicy
  | 0 => SourceScheduledCapabilityAnnotations.recipePolicy
  | depth + 1 => extendCapability (capability depth)

@[instance_reducible] def admission (depth : Nat) : SourceScheduledChecks.DeclarationPolicy where
  accepts := fun _outward required {_ _} plans => (capability depth).accepts required plans

@[instance_reducible] def certification : Nat → SourcePlannedChecks.DeclarationPolicy
  | 0 => SourcePlannedChecks.contextualPolicy
  | depth + 1 => extendCertification (capability depth) (certification depth)

/-- Induction over declaration evidence gives checked policy laws at every
finite layer. The operational calculus and continuation checks are unchanged. -/
theorem laws (depth : Nat) (outward : List Instance) :
    DeclarationLaws (capability depth) (admission depth) (certification depth) outward := by
  induction depth with
  | zero => exact SourceScheduledCapabilityAnnotations.recipeLaws outward
  | succ depth ih => exact extend_laws ih

theorem projection (depth : Nat) :
    SourceScheduledChecks.DeclarationProjection (admission depth) (certification depth) :=
  ⟨fun {outward _ _ _ _} checked => (laws depth outward).projected checked⟩

/-- Admission and capability reconstruction use the same structural evidence. -/
theorem admission_iff {plans : ClausePlans clauses families} :
    (admission depth).accepts outward required plans ↔ (capability depth).accepts required plans := Iff.rfl

theorem capability_inclusion {plans : ClausePlans clauses families}
    (checked : (capability depth).accepts required plans) :
    (capability (depth + 1)).accepts required plans := Or.inr (Or.inl checked)

theorem certification_inclusion {plans : ClausePlans clauses families}
    (checked : (certification depth).accepts outward required plans) :
    (certification (depth + 1)).accepts outward required plans := Or.inr (Or.inl checked)

theorem bounded_admitted {plans : ClausePlans clauses families}
    (checked : bounded (capability depth) required plans) :
    (capability (depth + 1)).accepts required plans := Or.inr (Or.inr checked)

end Ash.OneShot.SourceConsumingDeclarationPolicies

#print axioms Ash.OneShot.SourceConsumingDeclarationPolicies.extend_laws
#print axioms Ash.OneShot.SourceConsumingDeclarationPolicies.laws
#print axioms Ash.OneShot.SourceConsumingDeclarationPolicies.projection
#print axioms Ash.OneShot.SourceConsumingDeclarationPolicies.admission_iff
#print axioms Ash.OneShot.SourceConsumingDeclarationPolicies.capability_inclusion
#print axioms Ash.OneShot.SourceConsumingDeclarationPolicies.certification_inclusion
#print axioms Ash.OneShot.SourceConsumingDeclarationPolicies.bounded_admitted
