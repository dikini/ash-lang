import SourcePlannedTransport
import SourceDependencyReduction

/-! Closed substitution preserves stable annotations, including latent function
signatures and declarations installed later. Existing hereditary substitution
supplies all value/effect/owner indices; this proof handles only annotations. -/
namespace Ash.OneShot.SourcePlannedTyping
open ScopedExpressions ScopedExecution
open SourcePlanSignatures (substituteClauses substitution_signature)

namespace Values

theorem change_scope
    (source : Annotation operations contracts world scope environment code value signature)
    (isValue : code.IsValue) (next : Execution.Scope) :
    Annotation operations contracts world next environment code value signature := by
  induction source using Annotation.rec
    (motive_2 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ => True) with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference => exact .reference
  | lambda body ih => exact .lambda body
  | purePair left right ihLeft ihRight => exact .purePair (ihLeft isValue.1) (ihRight isValue.2)
  | pair left right ihLeft ihRight => exact .pair (ihLeft isValue.1) (ihRight isValue.2)
  | «variable» | app | bind | branch | perform | handler | resume | discard | cleanup | resource => cases isValue
  | unavailable | available | nil | cons => trivial

theorem summary
    (source : Annotation operations contracts world scope environment code value signature)
    (isValue : code.IsValue) : Annotation operations contracts world scope environment code value .pure := by
  induction source using Annotation.rec
    (motive_2 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ => True) with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference => exact .reference
  | lambda body ih => exact .lambda body
  | purePair left right ihLeft ihRight | pair left right ihLeft ihRight => exact .purePair (ihLeft isValue.1) (ihRight isValue.2)
  | «variable» | app | bind | branch | perform | handler | resume | discard | cleanup | resource => cases isValue
  | unavailable | available | nil | cons => trivial

theorem closed_environment
    (source : Annotation operations contracts world scope environment code value signature)
    (closed : ClosedValue code) (destination : Environment) :
    Annotation operations contracts world scope destination code value signature :=
  source.environment_congr (fun _ member => False.elim (ScopedTyping.closedValue_no_variable closed member))

end Values

theorem Annotation.substitution_at
    (source : Annotation operations contracts world scope sourceEnvironment code result signature) :
    ∀ environment name input value, sourceEnvironment = environment.extend name input →
      Annotation operations contracts world .none environment value input .pure → ClosedValue value →
      Annotation operations contracts world scope environment (code.subst name value) result signature := by
  induction source using Annotation.rec
    (motive_2 := fun contracts world sourceEnvironment parameter binder argument input answer resumeEffects closeEffects code held _ plans _ =>
      ∀ environment name valueType value, sourceEnvironment = environment.extend name valueType →
      Annotation operations contracts world .none environment value valueType .pure → ClosedValue value →
      Offer operations contracts world environment parameter binder argument input answer resumeEffects closeEffects
        (if name = parameter then code else code.subst name value) held plans)
    (motive_3 := fun contracts world sourceEnvironment effect answer _ _ plans _ =>
      ∀ environment name input value, sourceEnvironment = environment.extend name input →
      Annotation operations contracts world .none environment value input .pure → ClosedValue value →
      Declarations operations contracts world environment effect answer (substituteClauses plans name value)) with
  | unit | boolean | integer | reference =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      first | exact .unit | exact .boolean | exact .integer | exact .reference
  | «variable» known =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      simp only [Code.subst]
      split
      · rename_i same
        subst name
        simp only [Environment.extend, ↓reduceIte] at known
        cases Option.some.inj known
        exact Values.change_scope replacement closed.1 _
      · rename_i different
        exact .variable (by simpa [Environment.extend, Ne.symm different] using known)
  | lambda body ih =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      simp only [Code.subst]
      apply Annotation.lambda
      split
      · rename_i same
        subst name
        simpa only [Environment.extend_shadow] using body
      · rename_i different
        exact ih _ name input value (Environment.extend_commute environment name _ input _ different)
          (Values.closed_environment replacement closed _) closed
  | purePair left right ihLeft ihRight =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      exact .purePair (ihLeft environment name input value rfl replacement closed) (ihRight environment name input value rfl replacement closed)
  | pair left right ihLeft ihRight =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      exact .pair (ihLeft environment name input value rfl replacement closed) (ihRight environment name input value rfl replacement closed)
  | app function argument ihFunction ihArgument =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      exact .app (ihFunction environment name input value rfl replacement closed) (ihArgument environment name input value rfl replacement closed)
  | bind initial body ihInitial ihBody =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      apply Annotation.bind (ihInitial environment name input value rfl replacement closed)
      split
      · rename_i same
        subst name
        simpa only [Environment.extend_shadow] using body
      · rename_i different
        exact ihBody _ name input value (Environment.extend_commute environment name _ input _ different)
          (Values.closed_environment replacement closed _) closed
  | branch condition yes no ihCondition ihYes ihNo =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      exact .branch (ihCondition environment name input value rfl replacement closed)
        (ihYes environment name input value rfl replacement closed) (ihNo environment name input value rfl replacement closed)
  | perform known operand ih =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      exact .perform known (ih environment name input value rfl replacement closed)
  | handler body declarations ihBody ihDeclarations =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      simp only [Code.subst]
      rw [← substitution_signature _ (name := name) closed.1]
      exact .handler (ihBody environment name input value rfl replacement closed)
        (ihDeclarations environment name input value rfl replacement closed)
  | resume known resolved operand ih =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      exact .resume known resolved (ih environment name input value rfl replacement closed)
  | discard known resolved =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      exact .discard known resolved
  | cleanup callback body ihCallback ihBody =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      exact .cleanup (ihCallback environment name input value rfl replacement closed) (ihBody environment name input value rfl replacement closed)
  | resource initial body ihInitial ihBody =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      apply Annotation.resource (ihInitial environment name input value rfl replacement closed)
      intro identity fresh
      rw [Code.instantiation_subst _ name value _ closed.2.1]
      exact ihBody identity fresh environment name input value rfl
        (replacement.world_weaken (List.subset_append_left _ _)) closed
  | unavailable => exact .unavailable
  | available family ih =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      apply Offer.available
      intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
      split
      · rename_i same
        subst name
        simpa only [Environment.extend_shadow] using
          family owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
      · rename_i different
        exact ih owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance _ name input value
          (Environment.extend_commute environment name _ input _ different)
          (Values.closed_environment (replacement.extension (insert_extends _ fresh)) closed _) closed
  | nil => exact .nil
  | cons known ordinary protectedMode rest ihOrdinary ihProtected ihRest =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      exact .cons known (ihOrdinary environment name input value rfl replacement closed)
        (ihProtected environment name input value rfl replacement closed) (ihRest environment name input value rfl replacement closed)

theorem Annotation.substitution
    (source : Annotation operations contracts world scope (environment.extend name input) code result signature)
    (replacement : Annotation operations contracts world .none environment value input .pure) (closed : ClosedValue value) :
    Annotation operations contracts world scope environment (code.subst name value) result signature :=
  source.substitution_at environment name input value rfl replacement closed

/-- Reuse the old closed substitution theorem for all its semantic indices;
combine it with annotation substitution at exactly the same resulting code. -/
theorem Typed.substitution
    (source : Typed operations policy contracts world allowed scope (environment.extend name input) code result demand requirements signature)
    (replacement : Typed operations policy contracts world allowed .none environment value input [] (.request [] []) .pure)
    (closed : ClosedValue value) :
    Typed operations policy contracts world allowed scope environment (code.subst name value) result demand requirements signature := by
  constructor
  · exact SourceDependencyAnnotations.substitution
      (by simpa only [environment_erase_extend] using source.source) replacement.source closed
  · exact source.annotation.substitution replacement.annotation closed

/-- Bind reduction preserves the exact stable body signature. The old reduction
proof supplies unchanged requirement evaluation and ownership demand. -/
theorem Typed.bind_expression
    (source : Typed operations policy contracts world allowed scope environment (.bind parameter value body)
      result demand requirements (.sequence initialSignature bodySignature)) (closed : ClosedValue value) :
    ∃ reduced, Typed operations policy contracts world allowed scope environment (body.subst parameter value)
      result demand reduced bodySignature ∧
      ∀ store receiving before, RecursiveRequirements.evaluate store receiving before reduced =
        RecursiveRequirements.evaluate store receiving before requirements := by
  obtain ⟨reduced, remaining, next, ⟨initial, same, silent⟩, evaluation⟩ :=
    SourceDependencyAnnotations.bind_expression source.source closed
  have bodySame := (SourceDependencyAnnotations.Dependencies.sequence.inj same).2
  cases bodySame
  refine ⟨reduced, ⟨next, ?_⟩, evaluation⟩
  cases source.annotation with
  | bind initializer body =>
      exact body.substitution (Values.change_scope (Values.summary initializer closed.1) closed.1 .none) closed

/-- Beta reduction exposes the function's declared stable signature. Both
independent derivations describe the same substituted code and result type. -/
theorem Typed.beta_expression
    (source : Typed operations policy contracts world allowed scope environment (.app (.lambda parameter body) value)
      result demand requirements (.sequence functionSignature (.sequence argumentSignature bodySignature)))
    (closed : ClosedValue value) :
    ∃ reduced, Typed operations policy contracts world allowed .none environment (body.subst parameter value)
      result demand reduced bodySignature ∧
      ∀ store receiving before, RecursiveRequirements.evaluate store receiving before reduced =
        RecursiveRequirements.evaluate store receiving before requirements := by
  obtain ⟨reduced, remaining, next, ⟨functionDep, argumentDep, same, silentFunction, silentArgument⟩, evaluation⟩ :=
    SourceDependencyAnnotations.beta_expression source.source closed
  have bodySame := (SourceDependencyAnnotations.Dependencies.sequence.inj
    (SourceDependencyAnnotations.Dependencies.sequence.inj same).2).2
  cases bodySame
  refine ⟨reduced, ⟨next, ?_⟩, evaluation⟩
  cases source.annotation with
  | app function argument =>
      exact function.lambda_body.substitution
        (Values.change_scope (Values.summary argument closed.1) closed.1 .none) closed

/-- Fresh resource opening keeps the same family member of the stable signature
and reuses the old instantiated source derivation at the enlarged world. -/
theorem Typed.resource_body
    (source : Typed operations policy contracts world allowed scope environment (.resource binder initial code)
      output demand requirements (.sequence initialSignature (.resource bodySignatures)))
    (fresh : identity ∉ world) :
    ∃ residual bodyDemand bodyRequirements,
      Typed operations policy contracts (world ++ [identity]) (.cell identity :: residual) scope environment
        (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output bodyDemand bodyRequirements
        (bodySignatures identity) := by
  cases source.source with
  | resource initializer body formed effectsBound admitted hidden =>
      refine ⟨_, _, _, ⟨body identity fresh, ?_⟩⟩
      cases source.annotation with
      | resource initializer body => exact body identity fresh

namespace Examples
open SourceDependencyAnnotations.Examples (effectE effectF policy allowed cleanupBody cleanupRow functionCode boundProgram
  cleanupDependencies boundDependencies noRequirements invokedRequirements)
open SourcePlanSignatures (Signature)

def operations : Operations := fun _ _ => some (.unit, .unit)
def contracts : Contracts := fun _ => none
def environment : Environment := fun _ => none

def cleanupSignature : Signature cleanupDependencies :=
  .sequence .pure (.cleanup (.sequence .pure .request) (.sequence .pure .request))
def functionType : Value := .function .unit .unit allowed cleanupRow cleanupSignature

theorem function_typed : Typed operations policy contracts [] allowed .none environment functionCode functionType
    [] noRequirements .pure :=
  ⟨SourceDependencyAnnotations.Examples.function_source,
    .lambda (.cleanup (latent := [⟨effectF, 0, false⟩]) (.lambda (.perform rfl .unit)) (.perform rfl .unit))⟩

theorem bound_typed : Typed operations policy contracts [] allowed .none environment boundProgram .unit
    [] (.sequence noRequirements invokedRequirements)
    (.sequence .pure (.sequence .pure (.sequence .pure cleanupSignature))) :=
  ⟨SourceDependencyAnnotations.Examples.bound_function_retains_cleanup,
    .bind function_typed.annotation (.app (.variable rfl) .unit)⟩

/-- The existing higher-order execution now retains the stable cleanup
signature through both actual substitutions, with the same requirement checks. -/
theorem higher_order_signatures : ∃ first second,
    Typed operations policy contracts [] allowed .none environment (.app functionCode .unit) .unit [] first
      (.sequence .pure (.sequence .pure cleanupSignature)) ∧
    Typed operations policy contracts [] allowed .none environment cleanupBody .unit [] second cleanupSignature ∧
    ∀ store receiving before,
      RecursiveRequirements.evaluate store receiving before first =
        RecursiveRequirements.evaluate store receiving before (.sequence noRequirements invokedRequirements) ∧
      RecursiveRequirements.evaluate store receiving before second =
        RecursiveRequirements.evaluate store receiving before first := by
  obtain ⟨first, bound, bindEvaluation⟩ := bound_typed.bind_expression
    SourceDependencyAnnotations.Examples.annotated_function_closed
  obtain ⟨second, beta, betaEvaluation⟩ := bound.beta_expression CallableProtection.Examples.unit_closed
  exact ⟨first, second, bound, beta, fun store receiving before =>
    ⟨bindEvaluation store receiving before, betaEvaluation store receiving before⟩⟩

end Examples

end Ash.OneShot.SourcePlannedTyping

#print axioms Ash.OneShot.SourcePlannedTyping.Values.change_scope
#print axioms Ash.OneShot.SourcePlannedTyping.Values.summary
#print axioms Ash.OneShot.SourcePlannedTyping.Values.closed_environment
#print axioms Ash.OneShot.SourcePlannedTyping.Annotation.substitution_at
#print axioms Ash.OneShot.SourcePlannedTyping.Annotation.substitution
#print axioms Ash.OneShot.SourcePlannedTyping.Typed.substitution

#print axioms Ash.OneShot.SourcePlannedTyping.Typed.bind_expression
#print axioms Ash.OneShot.SourcePlannedTyping.Typed.beta_expression

#print axioms Ash.OneShot.SourcePlannedTyping.Examples.function_typed
#print axioms Ash.OneShot.SourcePlannedTyping.Examples.bound_typed
#print axioms Ash.OneShot.SourcePlannedTyping.Examples.higher_order_signatures

#print axioms Ash.OneShot.SourcePlannedTyping.Typed.resource_body
