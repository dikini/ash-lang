import SourcePlannedSourceTransport
import SourcePlannedContexts

/-! Closed substitution preserves the synchronized derivation. Existing
substitution, clause usage, port typing and instantiation proofs supply their
original obligations; signature preservation additionally retargets the actual
clause witness. Intermediate value choices remain shared after substitution. -/
namespace Ash.OneShot.SourcePlannedSources
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements)
open SourcePlannedTyping (Value Environment Operations Contract Contracts insert_extends)
open SourcePlanSignatures (substituteClauses substitution_signature)

namespace Values

theorem change_context
    (source : Expression operations policy contracts world allowed scope environment code value demand requirements dependencies)
    (isValue : code.IsValue) (nextAllowed : List Instance) (nextScope : Execution.Scope) :
    Expression operations policy contracts world nextAllowed nextScope environment code value demand requirements dependencies := by
  induction source using Expression.rec
      (motive_2 := fun _ _ _ _ _ _ _ _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ _ _ _ _ _ => True) with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | lambda body outward formed latentBound ih => exact .lambda body outward formed latentBound
  | purePair left right ihLeft ihRight => exact .purePair (ihLeft isValue.1) (ihRight isValue.2)
  | pair left right ihLeft ihRight => exact .pair (ihLeft isValue.1) (ihRight isValue.2)
  | «variable» | app | bind | branch | perform | handler | resume | discard | cleanup | resource => cases isValue
  | typed | unavailable | available | nil | cons => trivial

/-- Normalize only a value's immediate checking nodes. Its latent function
annotations and the ordinary value type remain exactly the same. -/
theorem summary
    (source : Expression operations policy contracts world allowed scope environment code value demand requirements dependencies)
    (isValue : code.IsValue) : ValueSummary operations policy contracts world environment allowed code value :=
  value_summary source isValue

theorem change_allowed (source : ValueSummary operations policy contracts world environment allowed code value)
    (isValue : code.IsValue) (next : List Instance) :
    ValueSummary operations policy contracts world environment next code value := change_context source isValue next .none

theorem closed_environment (source : ValueSummary operations policy contracts world environment allowed code value)
    (closed : ClosedValue code) (destination : Environment) :
    ValueSummary operations policy contracts world destination allowed code value :=
  expression_environment_congr source (fun _ member => False.elim (ScopedTyping.closedValue_no_variable closed member))

theorem world_weaken (source : ValueSummary operations policy contracts world environment allowed code value)
    (larger : world ⊆ next) : ValueSummary operations policy contracts next environment allowed code value :=
  expression_world_weaken source larger

theorem extension (source : ValueSummary operations policy contracts world environment allowed code value)
    (grows : contracts.Extends next) : ValueSummary operations policy next world environment allowed code value :=
  expression_extension source grows

/-- Reuse the existing port and usage projections for substituted values. -/
theorem erase (source : ValueSummary operations policy contracts world environment allowed code value)
    (isValue : code.IsValue) :
    SourceTemplates.ValueSummary operations.erase.erase policy contracts.erase.erase world environment.erase.erase allowed code value.erase.erase :=
  SourceDependencyAnnotations.Values.erase (expression_erase source) isValue

end Values

theorem substitution_at
    (source : Expression operations policy contracts world allowed scope sourceEnvironment code result demand requirements dependencies) :
    ∀ environment name input value, sourceEnvironment = environment.extend name input →
      ValueSummary operations policy contracts world environment allowed value input → ClosedValue value →
      Expression operations policy contracts world allowed scope environment (code.subst name value) result demand requirements dependencies := by
  induction source using Expression.rec
      (motive_2 := fun contracts world allowed scope sourceEnvironment code result header _ dependencies _ =>
        ∀ environment name input value, sourceEnvironment = environment.extend name input →
          ValueSummary operations policy contracts world environment allowed value input → ClosedValue value →
          Body operations policy contracts world allowed scope environment (code.subst name value) result header dependencies)
      (motive_3 := fun contracts world sourceEnvironment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row _ dependencies _ =>
        ∀ environment name valueType value, sourceEnvironment = environment.extend name valueType →
          ValueSummary operations policy contracts world environment allowed value valueType → ClosedValue value →
          Offer operations policy contracts world environment allowed parameter binder argument input answer resumeEffects closeEffects
            (if name = parameter then code else code.subst name value) held disposes row dependencies)
      (motive_4 := fun contracts world sourceEnvironment allowed effect answer clauses table _ dependencies _ =>
        ∀ environment name input value, sourceEnvironment = environment.extend name input →
          ValueSummary operations policy contracts world environment allowed value input → ClosedValue value →
          Declarations operations policy contracts world environment allowed effect answer (clauses.subst name value) table (substituteClauses dependencies name value)) with
  | unit | boolean | integer | reference =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      first | exact .unit | exact .boolean | exact .integer | apply Expression.reference; assumption
  | «variable» known formed =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      simp only [Code.subst]
      split
      · rename_i same
        subst name
        simp only [Environment.extend, ↓reduceIte] at known
        cases Option.some.inj known
        exact Values.change_context replacement closed.1 _ _
      · rename_i different
        exact .variable (by simpa [Environment.extend, Ne.symm different] using known) formed
  | lambda body outward formed latentBound ih =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      simp only [Code.subst]
      apply Expression.lambda _ outward formed latentBound
      split
      · rename_i same
        subst name
        simpa only [Environment.extend_shadow] using body
      · rename_i different
        exact ih _ name input value (Environment.extend_commute environment name _ input _ different)
          (Values.change_allowed (Values.closed_environment replacement closed _) closed.1 _) closed
  | purePair left right ihLeft ihRight =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      exact .purePair (ihLeft environment name input value rfl replacement closed) (ihRight environment name input value rfl replacement closed)
  | pair left right ihLeft ihRight =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      exact .pair (ihLeft environment name input value rfl replacement closed) (ihRight environment name input value rfl replacement closed)
  | app function argument admitted ihFunction ihArgument =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      exact .app (ihFunction environment name input value rfl replacement closed) (ihArgument environment name input value rfl replacement closed) admitted
  | bind initializer body ihInit ihBody =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      apply Expression.bind (ihInit environment name input value rfl replacement closed)
      split
      · rename_i same
        subst name
        simpa only [Environment.extend_shadow] using body
      · rename_i different
        exact ihBody _ name input value (Environment.extend_commute environment name _ input _ different)
          (Values.closed_environment replacement closed _) closed
  | branch condition yes no same ihCondition ihYes ihNo =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      exact .branch (ihCondition environment name input value rfl replacement closed) (ihYes environment name input value rfl replacement closed) (ihNo environment name input value rfl replacement closed) same
  | perform known admitted operand formed ih =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      exact .perform known admitted (ih environment name input value rfl replacement closed) formed
  | handler body clauses capabilities coverage unique admitted table modes declarations ihBody ihDecl =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      have changed := ScopedPorts.clauses_typed_substitution
        (by simpa only [SourcePlannedTyping.environment_erase_extend, SourceDependencyAnnotations.environment_erase_extend, CoherentSourceTypes.ports_extend] using clauses)
        ((Values.erase (Values.change_allowed replacement closed.1 []) closed.1).ports .none) closed
      have changedUsage := ScopedExpressions.clauses_usage_substitution capabilities closed.1
        (SourceCallableTransport.value_usage (Values.erase replacement closed.1)) name
      simp only [Code.subst]
      rw [← substitution_signature _ (name := name) closed.1]
      exact .handler
        (ihBody environment name input value rfl (Values.change_allowed replacement closed.1 _) closed)
        changed changedUsage
        (by simpa only [ScopedPorts.Covers, ScopedTyping.clause_keys_substitution] using coverage)
        (by simpa only [ScopedTyping.clause_keys_substitution] using unique) admitted table
        (SourceTemplates.clause_modes_substitution modes closed.1 name)
        (ihDecl environment name input value rfl (Values.change_allowed replacement closed.1 _) closed)
  | resume known resolved permission operand admitted formed ih =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      exact .resume known resolved permission (ih environment name input value rfl replacement closed) admitted formed
  | discard known resolved permission unprotected admitted =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      exact .discard known resolved permission unprotected admitted
  | cleanup callback body admitted ihCallback ihBody =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      exact .cleanup (ihCallback environment name input value rfl replacement closed) (ihBody environment name input value rfl replacement closed) admitted
  | resource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      apply Expression.resource (ihInit environment name input value rfl replacement closed) _ formed effectsBound admitted hidden
      intro identity fresh
      rw [Code.instantiation_subst _ name value _ closed.2.1]
      exact ihBody identity fresh environment name input value rfl
        (Values.change_allowed (Values.world_weaken replacement (List.subset_append_left _ _)) closed.1 _) closed
  | typed body rows closingRows ih =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      exact .typed (ih environment name input value rfl replacement closed) rows closingRows
  | unavailable =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      exact .unavailable
  | available resumeInterface closeInterface family ih =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      apply Offer.available
        (by split <;> simpa only [Code.substitution_required_actions _ _ closed.1] using resumeInterface)
        (by split <;> simpa only [Code.substitution_required_actions _ _ closed.1] using closeInterface)
      intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
      split
      · rename_i same
        subst name
        simpa only [Environment.extend_shadow] using
          family owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
      · rename_i different
        exact ih owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance _ name input value
          (Environment.extend_commute environment name _ input _ different)
          (Values.closed_environment
            (Values.extension replacement (insert_extends _ fresh)) closed _) closed
  | nil =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      exact .nil
  | cons known ordinary protectedMode rest ihOrdinary ihProtected ihRest =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      exact .cons known (ihOrdinary environment name input value rfl replacement closed) (ihProtected environment name input value rfl replacement closed) (ihRest environment name input value rfl replacement closed)

theorem substitution
    (source : Expression operations policy contracts world allowed scope (environment.extend name input) code result demand requirements dependencies)
    (replacement : ValueSummary operations policy contracts world environment allowed value input) (closed : ClosedValue value) :
    Expression operations policy contracts world allowed scope environment (code.subst name value) result demand requirements dependencies :=
  substitution_at source environment name input value rfl replacement closed

end Ash.OneShot.SourcePlannedSources

#print axioms Ash.OneShot.SourcePlannedSources.Values.change_context

#print axioms Ash.OneShot.SourcePlannedSources.Values.summary

#print axioms Ash.OneShot.SourcePlannedSources.Values.change_allowed

#print axioms Ash.OneShot.SourcePlannedSources.Values.closed_environment

#print axioms Ash.OneShot.SourcePlannedSources.Values.world_weaken

#print axioms Ash.OneShot.SourcePlannedSources.Values.extension

#print axioms Ash.OneShot.SourcePlannedSources.Values.erase

#print axioms Ash.OneShot.SourcePlannedSources.substitution_at

#print axioms Ash.OneShot.SourcePlannedSources.substitution
