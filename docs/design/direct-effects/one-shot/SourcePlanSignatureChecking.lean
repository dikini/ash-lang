import SourcePlanSignatures
import SourcePlannedChecks
import SourcePlannedTyping

/-! The stable plan signature is sufficient for the structural local checks.
This does not identify different source programs: full source typing must still
authenticate each actual clause against its plan. -/
namespace Ash.OneShot.SourcePlanSignatureChecking
open ScopedExpressions
open SourceDeclarationPlans (Plan ModePlans ClausePlans)
open SourcePlanSignatures
open SourcePlannedChecks (Certified CertifiedModes CertifiedClauses Local Pending)
open SourceContextualRequirements (DeclarationRecipes)

/-- Declaration recipes inspect clause order and required continuation actions;
reuse the same recipes when an authenticated clause witness changes. -/
theorem recipes_congr {first : ClausePlans before families} {second : ClausePlans after families}
    (recipes : DeclarationRecipes outward before families required)
    (same : clauseSignatures first = clauseSignatures second) :
    DeclarationRecipes outward after families required := by
  induction recipes generalizing after with
  | nil => cases first; cases second; exact .nil
  | cons ordinary protectedMode rest ih =>
      cases first with
      | cons firstOrdinary firstProtected firstRest =>
          cases second with
          | cons secondOrdinary secondProtected secondRest =>
              obtain ⟨actions, _, _, tail⟩ := ClauseSignatures.cons.inj same
              exact .cons (actions ▸ ordinary) (actions ▸ protectedMode) (ih tail)

/- Certification transport needs only a source declaration checker that
respects stable signatures. This parameter is a structural source law, not an
execution or future-body admission premise. -/
section
variable [evidence : SourcePlannedChecks.DeclarationPolicy]
variable (stable : ∀ {before after families required}
  {first : ClausePlans before families} {second : ClausePlans after families},
  evidence.accepts outward required first → clauseSignatures first = clauseSignatures second →
  evidence.accepts outward required second)
include stable

theorem certified_policy_congr (checked : Certified outward world first)
    (same : signature first = signature second) : Certified outward world second := by
  induction checked using Certified.rec
    (motive_2 := fun world _ first _ => ∀ {second}, modeSignatures first = modeSignatures second → CertifiedModes outward world second)
    (motive_3 := fun world _ _ first _ => ∀ {after} {second : ClausePlans after _},
      clauseSignatures first = clauseSignatures second → CertifiedClauses outward world second)
    with
  | pure => cases second; exact .pure
  | request => cases second; exact .request
  | invoke => cases second; exact .invoke
  | sequence left right ihLeft ihRight => cases second with
    | sequence nextLeft nextRight =>
        obtain ⟨leftSame, rightSame⟩ := Signature.sequence.inj same
        exact .sequence (ihLeft leftSame) (ihRight rightSame)
  | choice left right ihLeft ihRight => cases second with
    | choice nextLeft nextRight =>
        obtain ⟨leftSame, rightSame⟩ := Signature.choice.inj same
        exact .choice (ihLeft leftSame) (ihRight rightSame)
  | handler recipes declarations body ihDeclarations ihBody => cases second with
    | handler required plans body =>
        obtain ⟨rfl, declarationsSame, bodySame⟩ := Signature.handler.inj same
        exact .handler (stable recipes declarationsSame) (ihDeclarations declarationsSame) (ihBody bodySame)
  | cleanup callback body ihCallback ihBody => cases second with
    | cleanup nextCallback nextBody =>
        obtain ⟨callbackSame, bodySame⟩ := Signature.cleanup.inj same
        exact .cleanup (ihCallback callbackSame) (ihBody bodySame)
  | resource body ih => cases second with
    | resource next =>
        exact .resource (fun identity fresh => ih identity fresh (congrFun (Signature.resource.inj same) identity))
  | unavailable => rename_i second same; cases second; exact .unavailable
  | available body ih =>
      rename_i second same
      cases second with
      | available next => exact .available (fun owner => ih owner (congrFun (ModeSignatures.available.inj same) owner))
  | nil => rename_i after second same; cases second; exact .nil
  | cons ordinary protectedMode rest ihOrdinary ihProtected ihRest =>
      rename_i after second same
      cases second with
      | cons nextOrdinary nextProtected nextRest =>
          obtain ⟨_, ordinarySame, protectedSame, restSame⟩ := ClauseSignatures.cons.inj same
          exact .cons (ihOrdinary ordinarySame) (ihProtected protectedSame) (ihRest restSame)

theorem certified_modes_policy_congr (checked : CertifiedModes outward world first)
    (same : modeSignatures first = modeSignatures second) : CertifiedModes outward world second := by
  cases checked with
  | unavailable => cases second; exact .unavailable
  | available body => cases second with
    | available next => exact .available (fun owner => certified_policy_congr stable (body owner) (congrFun (ModeSignatures.available.inj same) owner))

theorem certified_clauses_policy_congr {first : ClausePlans before families} {second : ClausePlans after families}
    (checked : CertifiedClauses outward world first)
    (same : clauseSignatures first = clauseSignatures second) : CertifiedClauses outward world second := by
  induction checked using CertifiedClauses.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True) generalizing after with
  | nil => cases second; exact .nil
  | cons ordinary protectedMode rest ihOrdinary ihProtected ihRest => cases second with
    | cons nextOrdinary nextProtected nextRest =>
        obtain ⟨_, ordinarySame, protectedSame, restSame⟩ := ClauseSignatures.cons.inj same
        exact .cons (certified_modes_policy_congr stable ordinary ordinarySame) (certified_modes_policy_congr stable protectedMode protectedSame)
          (ihRest restSame)
  | pure | request | invoke | sequence | choice | handler | cleanup | resource | unavailable | available => trivial

end
/-- Existing recipe clients use the same signature transport proof. -/
theorem certified_congr (checked : Certified outward world first)
    (same : signature first = signature second) : Certified outward world second :=
  certified_policy_congr (fun recipes same => recipes_congr recipes same) checked same

theorem certified_modes_congr (checked : CertifiedModes outward world first)
    (same : modeSignatures first = modeSignatures second) : CertifiedModes outward world second :=
  certified_modes_policy_congr (fun recipes same => recipes_congr recipes same) checked same

theorem certified_clauses_congr {first : ClausePlans before families} {second : ClausePlans after families}
    (checked : CertifiedClauses outward world first)
    (same : clauseSignatures first = clauseSignatures second) : CertifiedClauses outward world second :=
  certified_clauses_policy_congr (fun recipes same => recipes_congr recipes same) checked same

/-- Every local rule can replace its actual plan by one with the same stable
signature. Pending checks keep their existing witnesses and runtime scopes. -/
theorem local_congr (checked : Local outward actions phases world first hints)
    (same : signature first = signature second) : Local outward actions phases world second hints := by
  refine (Local.rec
    (motive_1 := fun phases world _ _ first hints _ => ∀ {second},
      signature first = signature second → Local outward actions phases world second hints)
    (motive_2 := fun _ _ _ _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (t := checked)) same
  all_goals intros
  all_goals try trivial
  all_goals rename_i next same
  all_goals cases next
  all_goals first
    | exact .pure
    | exact .request ‹_› ‹_›
    | exact .resume ‹_› ‹_›
    | exact .dispose ‹_› ‹_›
    | (obtain ⟨leftSame, rightSame⟩ := Signature.sequence.inj same
       apply Local.sequence <;> first | apply_assumption; assumption)
    | (obtain ⟨leftSame, rightSame⟩ := Signature.choice.inj same
       apply Local.choice <;> first | apply_assumption; assumption)
    | (obtain ⟨rfl, declarationsSame, bodySame⟩ := Signature.handler.inj same
       exact .handler (recipes_congr ‹_› declarationsSame) (certified_clauses_congr ‹_› declarationsSame)
         ‹_› (by apply_assumption; exact bodySame))
    | (obtain ⟨callbackSame, bodySame⟩ := Signature.cleanup.inj same
       apply Local.cleanup <;> first | apply_assumption; assumption)
    | (have bodies := Signature.resource.inj same
       apply Local.resource
       intro identity fresh
       apply_assumption
       · exact fresh
       · exact congrFun bodies identity)

/-- Source annotation supplies the actual clause witness for handler entry.
Transport reuses the checked recipe at that witness's unchanged signature. -/
theorem actual_handler_checked {plans : ClausePlans before families}
    (annotated : SourcePlannedTyping.Annotation operations contracts world scope environment
      (.handle (Instantiation.freezeEffect effect) code arms) answer
      (signature (.handler (effect := effect) (table := table) required plans bodyPlan)))
    (checked : Local outward actions phases world (.handler (effect := effect) (table := table) required plans bodyPlan) hints) :
    ∃ actual : ClausePlans arms families,
      SourcePlannedTyping.Declarations operations contracts world environment effect answer actual ∧
      SourcePlannedTyping.Annotation operations contracts world scope environment code answer (signature bodyPlan) ∧
      Local outward actions phases world (.handler (effect := effect) (table := table) required actual bodyPlan) hints := by
  obtain ⟨actual, same, declarations, body⟩ := annotated.handler_declarations
  exact ⟨actual, declarations, body, local_congr checked (by simp only [signature, same])⟩

end Ash.OneShot.SourcePlanSignatureChecking

#print axioms Ash.OneShot.SourcePlanSignatureChecking.recipes_congr
#print axioms Ash.OneShot.SourcePlanSignatureChecking.certified_congr

#print axioms Ash.OneShot.SourcePlanSignatureChecking.certified_modes_congr
#print axioms Ash.OneShot.SourcePlanSignatureChecking.certified_clauses_congr
#print axioms Ash.OneShot.SourcePlanSignatureChecking.local_congr

#print axioms Ash.OneShot.SourcePlanSignatureChecking.actual_handler_checked

#print axioms Ash.OneShot.SourcePlanSignatureChecking.certified_policy_congr
#print axioms Ash.OneShot.SourcePlanSignatureChecking.certified_modes_policy_congr
#print axioms Ash.OneShot.SourcePlanSignatureChecking.certified_clauses_policy_congr
