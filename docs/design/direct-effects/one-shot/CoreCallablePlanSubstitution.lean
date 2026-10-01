import SourcePlanSignatures

/-! Deterministic substitution of visible common-contract checking plans.
The actual code guides operand positions and lexical shadowing. Public callable
contract-plan suffixes are retained. A mismatched shape is unchanged; source
soundness must independently establish the correspondence of code and plan.
This leaf does not enlarge source indices or admit new expression cases. -/
namespace Ash.OneShot.CoreCallablePlanSubstitution
open ScopedExpressions
open SourceDeclarationPlans (Plan ModePlans ClausePlans)
open SourcePlanSignatures (signature modeSignatures clauseSignatures Signature)

mutual
/-- Rewrite only visible source positions, preserving dependency indices. -/
def plan (code : Code) (source : Plan dependencies) (name : Nat) (value : Code) : Plan dependencies :=
  match source with
  | .sequence first second =>
    match code with
    | .pair left right => .sequence (plan left first name value) (plan right second name value)
    | .bind parameter initializer body =>
      .sequence (plan initializer first name value)
        (if name = parameter then second else plan body second name value)
    | .app function argument =>
      match second with
      | .sequence argumentPlan publicPlan =>
        .sequence (plan function first name value) (.sequence (plan argument argumentPlan name value) publicPlan)
      | other => .sequence first other
    | .branch condition yes no =>
      match second with
      | .choice yesPlan noPlan =>
        .sequence (plan condition first name value) (.choice (plan yes yesPlan name value) (plan no noPlan name value))
      | other => .sequence first other
    | .perform _ _ operand | .resume _ operand => .sequence (plan operand first name value) second
    | _ => .sequence first second
  | .handler required declarations bodyPlan =>
    match code with
    | .handle _ body _ => .handler required (clauses declarations name value) (plan body bodyPlan name value)
    | _ => .handler required declarations bodyPlan
  | other => other
termination_by structural source

/-- Available plans are rewritten pointwise over owner identities, independently
of the owner contract under which their source proof will be checked. -/
def modes (body : Code) (source : ModePlans family) (name : Nat) (value : Code) : ModePlans family :=
  match source with
  | .unavailable => .unavailable
  | .available bodies => .available (fun owner => plan body (bodies owner) name value)
termination_by structural source

/-- A clause parameter shadows substitution in its body and offered modes;
substitution always continues through the remaining declarations. -/
def clauses (source : ClausePlans arms families) (name : Nat) (value : Code) : ClausePlans (arms.subst name value) families :=
  match source with
  | .nil => .nil
  | @ClausePlans.cons ordinaryFamily protectedFamily rest restFamilies operation parameter binder body ordinary protectedMode restPlans =>
    if name = parameter then
      .cons ordinary protectedMode (clauses restPlans name value)
    else
      .cons (modes body ordinary name value) (modes body protectedMode name value) (clauses restPlans name value)
termination_by structural source
end

mutual
/-- Visible rewriting retains exact checking signatures. -/
theorem plan_signature (code : Code) (source : Plan dependencies) (name : Nat) (isValue : value.IsValue) :
    signature (plan code source name value) = signature source := by
  cases source with
  | pure | request | invoke | choice | cleanup | resource => rfl
  | sequence first second =>
    cases code <;> simp only [plan, signature] <;> try rfl
    · exact congr (congrArg Signature.sequence (plan_signature _ first name isValue)) (plan_signature _ second name isValue)
    · cases second <;> simp only [plan, signature]
      exact congr (congrArg Signature.sequence (plan_signature _ first name isValue))
        (congrArg (fun argument => Signature.sequence argument _) (plan_signature _ _ name isValue))
    · split
      · exact congrArg (fun initial => Signature.sequence initial _) (plan_signature _ first name isValue)
      · exact congr (congrArg Signature.sequence (plan_signature _ first name isValue)) (plan_signature _ second name isValue)
    · cases second <;> simp only [plan, signature]
      exact congr (congrArg Signature.sequence (plan_signature _ first name isValue))
        (congr (congrArg Signature.choice (plan_signature _ _ name isValue)) (plan_signature _ _ name isValue))
    · exact congrArg (fun operand => Signature.sequence operand _) (plan_signature _ first name isValue)
    · exact congrArg (fun operand => Signature.sequence operand _) (plan_signature _ first name isValue)
  | handler required declarations bodyPlan =>
    cases code <;> simp only [plan, signature] <;> try rfl
    exact congr (congrArg (Signature.handler required) (clauses_signature declarations name isValue))
      (plan_signature _ bodyPlan name isValue)
termination_by structural source

theorem modes_signature (body : Code) (source : ModePlans family) (name : Nat) (isValue : value.IsValue) :
    modeSignatures (modes body source name value) = modeSignatures source := by
  cases source with
  | unavailable => rfl
  | available bodies =>
    exact congrArg SourcePlanSignatures.ModeSignatures.available
      (funext (fun owner => plan_signature body (bodies owner) name isValue))
termination_by structural source

theorem clauses_signature (source : ClausePlans arms families) (name : Nat) (isValue : value.IsValue) :
    clauseSignatures (clauses source name value) = clauseSignatures source := by
  cases source with
  | nil => rfl
  | cons ordinary protectedMode rest =>
    simp only [clauses, clauseSignatures, Clauses.subst]
    split
    · rename_i same
      simp only [clauseSignatures, if_pos same]
      rw [clauses_signature rest name isValue]
    · rename_i different
      simp only [clauseSignatures, if_neg different, Code.substitution_required_actions _ _ isValue]
      rw [modes_signature _ ordinary name isValue, modes_signature _ protectedMode name isValue,
        clauses_signature rest name isValue]

termination_by structural source
end

end Ash.OneShot.CoreCallablePlanSubstitution
#print axioms Ash.OneShot.CoreCallablePlanSubstitution.plan_signature
#print axioms Ash.OneShot.CoreCallablePlanSubstitution.modes_signature
#print axioms Ash.OneShot.CoreCallablePlanSubstitution.clauses_signature
