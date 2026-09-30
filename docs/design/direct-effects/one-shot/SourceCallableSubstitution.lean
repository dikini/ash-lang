import SourceCallableTransport

/-! Closed value substitution for shared callable and recursive source evidence. -/
namespace Ash.OneShot.SourceCallableSubstitution
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts
open SourceTemplates (Expression CallableSummary ValueSummary)

mutual
theorem substitution
    (source : Expression operations policy contracts world allowed scope (environment.extend name input) code result demand requirements)
    (replacement : ValueSummary operations policy contracts world environment allowed value input) (closed : ClosedValue value) :
    Expression operations policy contracts world allowed scope environment (code.subst name value) result demand requirements := by
  cases source with
  | stable summary => exact .callable (callable_substitution
      (CallableSources.from_legacy summary (fun _ _ _ _ _ _ checked => .stable checked)) replacement closed)
  | callable summary => exact .callable (callable_substitution summary replacement closed)
  | lambda body outward formed =>
      rename_i requests bodyCode output bodyDemand bodyRequirements latent domain parameter
      by_cases same : name = parameter
      · subst parameter
        simp only [Code.subst, ↓reduceIte]
        exact .lambda (by simpa only [Environment.extend_shadow] using body) outward formed
      · simp only [Code.subst, if_neg same]
        have rearranged := body
        rw [Environment.extend_commute environment name parameter input domain same] at rearranged
        exact .lambda (substitution rearranged
          ((SourceCallableTransport.closed_value_environment replacement closed (environment.extend parameter domain)).change_allowed closed.1 requests) closed) outward formed
  | purePair left right => exact .purePair (substitution left replacement closed) (substitution right replacement closed)
  | pair left right => exact .pair (substitution left replacement closed) (substitution right replacement closed)
  | app function argument admitted => exact .app (substitution function replacement closed) (substitution argument replacement closed) admitted
  | bind initializer body =>
      rename_i a domain initializerDemand initializerRequirements parameter b bodyDemand bodyRequirements
      apply Expression.bind (substitution initializer replacement closed)
      by_cases same : name = parameter
      · subst parameter
        simpa only [ite_true, Environment.extend_shadow] using body
      · simp only [if_neg same]
        have rearranged := body
        rw [Environment.extend_commute environment name parameter input domain same] at rearranged
        exact substitution rearranged (SourceCallableTransport.closed_value_environment replacement closed (environment.extend parameter domain)) closed
  | branch condition yes no same =>
      exact .branch (substitution condition replacement closed) (substitution yes replacement closed) (substitution no replacement closed) same
  | handler body clauses capabilities coverage unique admitted table modes =>
      have changed := ScopedPorts.clauses_typed_substitution
        (by simpa only [ports_extend] using clauses)
        ((replacement.change_allowed closed.1 []).ports .none) closed
      have changedUsage := ScopedExpressions.clauses_usage_substitution capabilities closed.1
        (SourceCallableTransport.value_usage replacement) name
      exact .handler (substitution body (replacement.change_allowed closed.1 _) closed) changed changedUsage
        (by simpa only [ScopedPorts.Covers, ScopedTyping.clause_keys_substitution] using coverage)
        (by simpa only [ScopedTyping.clause_keys_substitution] using unique) admitted table (SourceTemplates.clause_modes_substitution modes closed.1 name)
  | perform known admitted operand formed => exact .perform known admitted (substitution operand replacement closed) formed
  | resource initializer body formed effectsBound admitted outward =>
      apply Expression.resource (substitution initializer replacement closed) _ formed effectsBound admitted outward
      intro identity fresh
      rw [Code.instantiation_subst _ name value _ closed.2.1]
      exact callable_substitution (body identity fresh)
        ((replacement.world_weaken (by simp)).change_allowed closed.1 _) closed
  | scopedResource initializer body formed effectsBound admitted hidden =>
      apply Expression.scopedResource (substitution initializer replacement closed) _ formed effectsBound admitted hidden
      intro identity fresh
      rw [Code.instantiation_subst _ name value _ closed.2.1]
      exact substitution (body identity fresh)
        ((replacement.world_weaken (by simp)).change_allowed closed.1 _) closed
  | resume known resolved permission operand admitted formed =>
      exact .resume known resolved permission (substitution operand replacement closed) admitted formed
  | discard known resolved permission unprotected admitted => exact .discard known resolved permission unprotected admitted
  | cleanup callback body admitted => exact .cleanup (substitution callback replacement closed) (substitution body replacement closed) admitted
termination_by (code.nodes, 1)
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals try simp only [Code.nodes]
  all_goals first
    | apply Prod.Lex.left; omega
    | apply Prod.Lex.right; omega

theorem callable_substitution
    (source : CallableSummary operations policy contracts world (environment.extend name input) allowed code result row)
    (replacement : ValueSummary operations policy contracts world environment allowed value input) (closed : ClosedValue value) :
    CallableSummary operations policy contracts world environment allowed (code.subst name value) result row := by
  cases source with
  | summaryUnit => exact .summaryUnit
  | summaryBoolean => exact .summaryBoolean
  | summaryInteger => exact .summaryInteger
  | summaryReference issued => exact .summaryReference issued
  | summaryVariable known formed =>
      simp only [Code.subst]
      split
      · rename_i same
        subst name
        simp only [Environment.extend, ↓reduceIte] at known
        cases Option.some.inj known
        exact SourceCallableTransport.value_callable replacement
      · rename_i different
        exact .summaryVariable (by simpa [Environment.extend, Ne.symm different] using known) formed
  | summaryPair left right => exact .summaryPair (callable_substitution left replacement closed) (callable_substitution right replacement closed)
  | summaryLambda body outward formed =>
      rename_i latentRequests bodyCode output bodyDemand bodyRequirements latentRow domain parameter
      by_cases same : name = parameter
      · subst parameter
        simp only [Code.subst, ↓reduceIte]
        exact .summaryLambda (by simpa only [Environment.extend_shadow] using body) outward formed
      · simp only [Code.subst, if_neg same]
        have rearranged := body
        rw [Environment.extend_commute environment name parameter input domain same] at rearranged
        exact .summaryLambda (substitution rearranged
          ((SourceCallableTransport.closed_value_environment replacement closed (environment.extend parameter domain)).change_allowed closed.1 latentRequests) closed) outward formed
  | summaryApp function argument admitted => exact .summaryApp (callable_substitution function replacement closed) (callable_substitution argument replacement closed) admitted
  | summaryBind initializer body =>
      rename_i a domain initializerRow parameter b bodyRow
      apply CallableSources.Summary.summaryBind (callable_substitution initializer replacement closed)
      by_cases same : name = parameter
      · subst parameter
        simpa only [ite_true, Environment.extend_shadow] using body
      · simp only [if_neg same]
        have rearranged := body
        rw [Environment.extend_commute environment name parameter input domain same] at rearranged
        exact callable_substitution rearranged (SourceCallableTransport.closed_value_environment replacement closed (environment.extend parameter domain)) closed
  | summaryBranch condition yes no => exact .summaryBranch (callable_substitution condition replacement closed) (callable_substitution yes replacement closed) (callable_substitution no replacement closed)
  | summaryPerform known admitted operand formed => exact .summaryPerform known admitted (callable_substitution operand replacement closed) formed
  | summaryCleanup callback body admitted => exact .summaryCleanup (callable_substitution callback replacement closed) (callable_substitution body replacement closed) admitted
  | summaryResource initializer body formed effectsBound admitted outward =>
      apply CallableSources.Summary.summaryResource (callable_substitution initializer replacement closed) _ formed effectsBound admitted outward
      intro identity fresh
      rw [Code.instantiation_subst _ name value _ closed.2.1]
      exact callable_substitution (body identity fresh)
        ((replacement.world_weaken (List.subset_append_left _ _)).change_allowed closed.1 _) closed
termination_by (code.nodes, 0)
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals try simp only [Code.nodes]
  all_goals first
    | apply Prod.Lex.left; omega
    | apply Prod.Lex.right; omega

end

end Ash.OneShot.SourceCallableSubstitution
#print axioms Ash.OneShot.SourceCallableSubstitution.substitution
#print axioms Ash.OneShot.SourceCallableSubstitution.callable_substitution
