import DeclaredSourceValues

/-! Closed substitution retains hereditary source declarations. Stable legacy
    summaries are embedded through the existing callable rules, so replacements
    may carry function bodies containing handlers. -/
namespace Ash.OneShot.DeclaredSourceSubstitution
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts
open DeclaredSources (Expression Callable Body Offer Declarations)
open DeclaredSourceValues (ValueSummary)
open RecursiveRequirements (Requirements)

theorem legacy_substitution
    (source : Summary operations world (environment.extend name input) allowed code result row)
    (replacement : ValueSummary operations policy contracts world environment allowed value input) (closed : ClosedValue value) :
    Callable operations policy contracts world environment allowed (code.subst name value) result row := by
  cases source with
  | unit => exact .summaryUnit
  | boolean => exact .summaryBoolean
  | integer => exact .summaryInteger
  | reference issued => exact .summaryReference issued
  | «variable» known formed =>
      simp only [Code.subst]
      split
      · rename_i same
        subst name
        simp only [Environment.extend, ↓reduceIte] at known
        cases Option.some.inj known
        exact replacement
      · rename_i different
        exact .summaryVariable (by simpa [Environment.extend, Ne.symm different] using known) formed
  | pair left right => exact .summaryPair (legacy_substitution left replacement closed) (legacy_substitution right replacement closed)
  | lambda body formed =>
      rename_i latentRequests bodyCode output latentRow domain parameter
      by_cases same : name = parameter
      · subst parameter
        simp only [Code.subst, ↓reduceIte]
        exact .summaryLambda (.stable (by simpa only [Environment.extend_shadow] using body)) (.request (layers := [])) formed
      · simp only [Code.subst, if_neg same]
        have rearranged := body
        rw [Environment.extend_commute environment name parameter input domain same] at rearranged
        exact .summaryLambda (.callable (legacy_substitution rearranged
          (DeclaredSourceValues.change_allowed (DeclaredSourceValues.closed_environment replacement closed (environment.extend parameter domain)) closed.1 latentRequests) closed)) (.request (layers := [])) formed
  | app function argument admitted => exact .summaryApp (legacy_substitution function replacement closed) (legacy_substitution argument replacement closed) admitted
  | bind initializer body =>
      rename_i a domain initializerRow parameter b bodyRow
      apply Callable.summaryBind (legacy_substitution initializer replacement closed)
      by_cases same : name = parameter
      · subst parameter
        exact DeclaredSourceValues.from_legacy (by simpa only [ite_true, Environment.extend_shadow] using body)
      · simp only [if_neg same]
        have rearranged := body
        rw [Environment.extend_commute environment name parameter input domain same] at rearranged
        exact legacy_substitution rearranged (DeclaredSourceValues.closed_environment replacement closed (environment.extend parameter domain)) closed
  | branch condition yes no => exact .summaryBranch (legacy_substitution condition replacement closed) (legacy_substitution yes replacement closed) (legacy_substitution no replacement closed)
  | perform known admitted operand formed => exact .summaryPerform known admitted (legacy_substitution operand replacement closed) formed
  | cleanup callback body admitted => exact .summaryCleanup (legacy_substitution callback replacement closed) (legacy_substitution body replacement closed) admitted
  | resource initializer body formed effectsBound admitted outward =>
      apply Callable.summaryResource (legacy_substitution initializer replacement closed) _ formed effectsBound admitted outward
      intro identity fresh
      rw [Code.instantiation_subst _ name value _ closed.2.1]
      exact legacy_substitution (body identity fresh)
        (DeclaredSourceValues.change_allowed (DeclaredSourceValues.world_weaken replacement (List.subset_append_left _ _)) closed.1 _) closed
termination_by code.nodes
decreasing_by all_goals subst_vars; all_goals simp only [Code.nodes, Code.instantiation_nodes]; all_goals omega


theorem substitution_at
    (source : Expression operations policy contracts world allowed scope sourceEnvironment code result demand requirements) :
    ∀ environment name input value, sourceEnvironment = environment.extend name input →
      ValueSummary operations policy contracts world environment allowed value input → ClosedValue value →
      Expression operations policy contracts world allowed scope environment (code.subst name value) result demand requirements := by
  induction source using Expression.rec
      (motive_2 := fun contracts world sourceEnvironment allowed code result row _ =>
        ∀ environment name input value, sourceEnvironment = environment.extend name input →
          ValueSummary operations policy contracts world environment allowed value input → ClosedValue value →
          Callable operations policy contracts world environment allowed (code.subst name value) result row)
      (motive_3 := fun contracts world allowed scope sourceEnvironment code result header _ =>
        ∀ environment name input value, sourceEnvironment = environment.extend name input →
          ValueSummary operations policy contracts world environment allowed value input → ClosedValue value →
          Body operations policy contracts world allowed scope environment (code.subst name value) result header)
      (motive_4 := fun contracts world sourceEnvironment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row _ =>
        ∀ environment name valueType value, sourceEnvironment = environment.extend name valueType →
          ValueSummary operations policy contracts world environment allowed value valueType → ClosedValue value →
          Offer operations policy contracts world environment allowed parameter binder argument input answer resumeEffects closeEffects
            (if name = parameter then code else code.subst name value) held disposes row)
      (motive_5 := fun contracts world sourceEnvironment allowed effect answer clauses table _ =>
        ∀ environment name input value, sourceEnvironment = environment.extend name input →
          ValueSummary operations policy contracts world environment allowed value input → ClosedValue value →
          Declarations operations policy contracts world environment allowed effect answer (clauses.subst name value) table) with
  | stable summary =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      exact .callable (legacy_substitution summary replacement closed)
  | callable summary ih =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      exact .callable (ih environment name input value rfl replacement closed)
  | lambda body outward formed ih =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      simp only [Code.subst]
      apply Expression.lambda _ outward formed
      split
      · rename_i same
        subst name
        simpa only [Environment.extend_shadow] using body
      · rename_i different
        exact ih _ name input value (Environment.extend_commute environment name _ input _ different)
          (DeclaredSourceValues.change_allowed (DeclaredSourceValues.closed_environment replacement closed _) closed.1 _) closed
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
          (DeclaredSourceValues.closed_environment replacement closed _) closed
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
        (by simpa only [ports_extend] using clauses)
        ((DeclaredSourceValues.erase (DeclaredSourceValues.change_allowed replacement closed.1 [])).ports .none) closed
      have changedUsage := ScopedExpressions.clauses_usage_substitution capabilities closed.1
        (SourceCallableTransport.value_usage (DeclaredSourceValues.erase replacement)) name
      exact .handler
        (ihBody environment name input value rfl (DeclaredSourceValues.change_allowed replacement closed.1 _) closed)
        changed changedUsage
        (by simpa only [ScopedPorts.Covers, ScopedTyping.clause_keys_substitution] using coverage)
        (by simpa only [ScopedTyping.clause_keys_substitution] using unique) admitted table
        (SourceTemplates.clause_modes_substitution modes closed.1 name)
        (ihDecl environment name input value rfl (DeclaredSourceValues.change_allowed replacement closed.1 _) closed)
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
  | resource initializer body formed effectsBound admitted outward ihInit ihBody =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      apply Expression.resource (ihInit environment name input value rfl replacement closed) _ formed effectsBound admitted outward
      intro identity fresh
      rw [Code.instantiation_subst _ name value _ closed.2.1]
      exact ihBody identity fresh environment name input value rfl
        (DeclaredSourceValues.change_allowed (DeclaredSourceValues.world_weaken replacement (List.subset_append_left _ _)) closed.1 _) closed
  | scopedResource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      intro environment name input value environmentSame replacement closed
      cases environmentSame
      apply Expression.scopedResource (ihInit environment name input value rfl replacement closed) _ formed effectsBound admitted hidden
      intro identity fresh
      rw [Code.instantiation_subst _ name value _ closed.2.1]
      exact ihBody identity fresh environment name input value rfl
        (DeclaredSourceValues.change_allowed (DeclaredSourceValues.world_weaken replacement (List.subset_append_left _ _)) closed.1 _) closed
  | summaryUnit =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      exact .summaryUnit
  | summaryBoolean =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      exact .summaryBoolean
  | summaryInteger =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      exact .summaryInteger
  | summaryReference issued =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      exact .summaryReference issued
  | summaryVariable known formed =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      simp only [Code.subst]
      split
      · rename_i same
        subst name
        simp only [Environment.extend, ↓reduceIte] at known
        cases Option.some.inj known
        exact replacement
      · rename_i different
        exact .summaryVariable (by simpa [Environment.extend, Ne.symm different] using known) formed
  | summaryPair left right ihLeft ihRight =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      exact .summaryPair (ihLeft environment name input value rfl replacement closed) (ihRight environment name input value rfl replacement closed)
  | summaryLambda body outward formed ih =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      simp only [Code.subst]
      apply Callable.summaryLambda _ outward formed
      split
      · rename_i same
        subst name
        simpa only [Environment.extend_shadow] using body
      · rename_i different
        exact ih _ name input value (Environment.extend_commute environment name _ input _ different)
          (DeclaredSourceValues.change_allowed (DeclaredSourceValues.closed_environment replacement closed _) closed.1 _) closed
  | summaryApp function argument admitted ihFunction ihArgument =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      exact .summaryApp (ihFunction environment name input value rfl replacement closed) (ihArgument environment name input value rfl replacement closed) admitted
  | summaryBind initializer body ihInit ihBody =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      apply Callable.summaryBind (ihInit environment name input value rfl replacement closed)
      split
      · rename_i same
        subst name
        simpa only [Environment.extend_shadow] using body
      · rename_i different
        exact ihBody _ name input value (Environment.extend_commute environment name _ input _ different)
          (DeclaredSourceValues.closed_environment replacement closed _) closed
  | summaryBranch condition yes no ihCondition ihYes ihNo =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      exact .summaryBranch (ihCondition environment name input value rfl replacement closed) (ihYes environment name input value rfl replacement closed) (ihNo environment name input value rfl replacement closed)
  | summaryPerform known admitted operand formed ih =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      exact .summaryPerform known admitted (ih environment name input value rfl replacement closed) formed
  | summaryCleanup callback body admitted ihCallback ihBody =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      exact .summaryCleanup (ihCallback environment name input value rfl replacement closed) (ihBody environment name input value rfl replacement closed) admitted
  | summaryResource initializer body formed effectsBound admitted outward ihInit ihBody =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      apply Callable.summaryResource (ihInit environment name input value rfl replacement closed) _ formed effectsBound admitted outward
      intro identity fresh
      rw [Code.instantiation_subst _ name value _ closed.2.1]
      exact ihBody identity fresh environment name input value rfl
        (DeclaredSourceValues.change_allowed (DeclaredSourceValues.world_weaken replacement (List.subset_append_left _ _)) closed.1 _) closed
  | typed body rows ih =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      exact .typed (ih environment name input value rfl replacement closed) rows
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
          (DeclaredSourceValues.closed_environment
            (DeclaredSourceValues.extension replacement (Owners.insert_extends _ fresh)) closed _) closed
  | nil =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      exact .nil
  | cons known ordinary protectedMode rest ihOrdinary ihProtected ihRest =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      exact .cons known (ihOrdinary environment name input value rfl replacement closed) (ihProtected environment name input value rfl replacement closed) (ihRest environment name input value rfl replacement closed)

theorem substitution
    (source : Expression operations policy contracts world allowed scope (environment.extend name input) code result demand requirements)
    (replacement : ValueSummary operations policy contracts world environment allowed value input) (closed : ClosedValue value) :
    Expression operations policy contracts world allowed scope environment (code.subst name value) result demand requirements :=
  substitution_at source environment name input value rfl replacement closed

theorem callable_substitution
    (source : Callable operations policy contracts world (environment.extend name input) allowed code result row)
    (replacement : ValueSummary operations policy contracts world environment allowed value input) (closed : ClosedValue value) :
    Callable operations policy contracts world environment allowed (code.subst name value) result row :=
  DeclaredSourceValues.request_callable
    (substitution (Expression.callable (scope := .none) source) replacement closed) row rfl


theorem body_substitution
    (source : Body operations policy contracts world allowed scope (environment.extend name input) code result header)
    (replacement : ValueSummary operations policy contracts world environment allowed value input) (closed : ClosedValue value) :
    Body operations policy contracts world allowed scope environment (code.subst name value) result header := by
  cases source with
  | typed body rows => exact .typed (substitution body replacement closed) rows

theorem offer_substitution
    (source : Offer operations policy contracts world (environment.extend name valueType) allowed
      parameter binder argument input answer resumeEffects closeEffects code held disposes row)
    (replacement : ValueSummary operations policy contracts world environment allowed value valueType) (closed : ClosedValue value) :
    Offer operations policy contracts world environment allowed parameter binder argument input answer resumeEffects closeEffects
      (if name = parameter then code else code.subst name value) held disposes row := by
  cases source with
  | unavailable => exact .unavailable
  | available resumeInterface closeInterface family =>
      apply Offer.available
        (by split <;> simpa only [Code.substitution_required_actions _ _ closed.1] using resumeInterface)
        (by split <;> simpa only [Code.substitution_required_actions _ _ closed.1] using closeInterface)
      intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
      have typed := family owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
      by_cases same : name = parameter
      · subst name
        simpa only [if_true, Environment.extend_shadow] using typed
      · rw [Environment.extend_commute environment name parameter valueType argument same] at typed
        simpa only [if_neg same] using body_substitution typed
          (DeclaredSourceValues.closed_environment
            (DeclaredSourceValues.extension replacement (Owners.insert_extends _ fresh)) closed _) closed

theorem declarations_substitution
    (source : Declarations operations policy contracts world (environment.extend name input) allowed effect answer clauses table)
    (replacement : ValueSummary operations policy contracts world environment allowed value input) (closed : ClosedValue value) :
    Declarations operations policy contracts world environment allowed effect answer (clauses.subst name value) table := by
  induction clauses using Clauses.rec (motive_1 := fun _ => True) generalizing table
  case nil => cases source; exact .nil
  case cons operation parameter binder body rest ihBody ihRest =>
    cases source with
    | cons known ordinary protectedMode rest =>
        exact .cons known (offer_substitution ordinary replacement closed) (offer_substitution protectedMode replacement closed) (ihRest rest)
  all_goals trivial

/-- Selection and payload binding preserve hereditary body evidence under the
    actual fresh contract. Effect-bound certificates are not assumed here. -/
theorem selected_payload
    (source : Declarations operations policy contracts world environment allowed requested answer clauses table)
    (selected : ClauseAt operation clauses parameter binder code)
    (found : lookup operation table = some offered)
    (available : offered.row held = some row)
    (operationKnown : operations requested operation = some (argument, input))
    (payload : ValueSummary operations policy contracts world environment allowed value argument)
    (closed : ClosedValue value) :
    ∃ resumeEffects closeEffects,
      ∀ owner (contract : Owners.Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = held → contract.closeDemand.Perm contract.resumeDemand →
        Body operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          environment (code.subst parameter value) contract.answer ⟨owner, contract, offered.dispose, row⟩ := by
  obtain ⟨declaredArgument, declaredInput, resumeEffects, closeEffects, signature, resumeInterface, closeInterface, family⟩ :=
    DeclaredSources.selected_body source selected found available
  have same := Option.some.inj (signature.symm.trans operationKnown)
  rcases Prod.mk.inj same with ⟨rfl, rfl⟩
  refine ⟨resumeEffects, closeEffects, ?_⟩
  intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
  have bound := body_substitution
    (family owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance)
    (DeclaredSourceValues.extension payload (Owners.insert_extends contracts fresh)) closed
  simpa only [answerSame] using bound

theorem beta_body
    (function : Expression operations policy contracts world allowed sourceScope environment
      (.lambda parameter code) (.function input output requests latent) functionDemand functionRequirements)
    (argument : ValueSummary operations policy contracts world environment allowed value input)
    (closed : ClosedValue value) (admitted : requests ⊆ allowed) :
    ∃ demand, ∃ requirements : Requirements demand,
      Expression operations policy contracts world allowed .none environment
        (code.subst parameter value) output demand requirements ∧
      RecursiveOutward.Outward requirements (some latent) := by
  obtain ⟨demand, requirements, body, outward⟩ := DeclaredSources.lambda_body function
  have replaced := substitution body (DeclaredSourceValues.change_allowed argument closed.1 requests) closed
  exact ⟨demand, requirements,
    DeclaredSourceTransport.expression_allowed_mono replaced admitted, outward⟩

/-- Actual beta reduction retains the hereditary body and its outward
    certificate. The existing RawStep.beta rule clears the continuation scope
    and leaves the stack unchanged; whole-state source preservation is a separate join. -/
theorem beta_source
    (function : Expression operations policy contracts world allowed scope Environment.empty
      (.lambda parameter code) (.function input output requests latent) functionDemand functionRequirements)
    (argument : ValueSummary operations policy contracts world Environment.empty allowed value input)
    (closed : ClosedValue value) (admitted : requests ⊆ allowed) :
    ∃ demand, ∃ requirements : Requirements demand,
      RawStep ⟨.app (.lambda parameter code) value, scope, stack⟩
        ⟨code.subst parameter value, .none, stack⟩ [] [] ∧
      Expression operations policy contracts world allowed .none Environment.empty
        (code.subst parameter value) output demand requirements ∧
      RecursiveOutward.Outward requirements (some latent) := by
  have functionClosed := ScopedPorts.typed_value_closed
    ((DeclaredSourceValues.erase (DeclaredSourceValues.value_summary function trivial)).ports .none) trivial
  obtain ⟨demand, requirements, body, outward⟩ := beta_body function argument closed admitted
  exact ⟨demand, requirements, .beta parameter code value scope stack closed functionClosed, body, outward⟩

namespace Examples
open SourceCallableExamples (operations policy contracts function functionType effect table operation_known)

theorem function_value : ValueSummary operations policy contracts [] Environment.empty [] function functionType :=
  DeclaredSourceValues.value_summary (DeclaredSources.Examples.function_source contracts Environment.empty .none) trivial

theorem function_closed : ClosedValue function :=
  ScopedPorts.typed_value_closed ((DeclaredSourceValues.erase function_value).ports .none) trivial

theorem substituted_stable_application :
    Expression operations policy contracts [] [] .none Environment.empty (.app function .unit) .unit [] (.request [] []) := by
  have source : Expression operations policy contracts [] [] .none (Environment.empty.extend 7 functionType)
      (.app (.variable 7) .unit) .unit [] (.request [] []) :=
    .stable (.app (.variable (by simp [Environment.extend, functionType])
      (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])) .unit (List.Subset.refl []))
  exact substitution source function_value function_closed

def variableClauses : Clauses := .cons 0 2 9 (.bind 5 (.resume 9 .unit) (.variable 7)) .nil

theorem variable_declaration :
    Declarations operations policy contracts [] (Environment.empty.extend 7 functionType) [] effect functionType variableClauses table := by
  have family : ∀ held, Offer operations policy contracts [] (Environment.empty.extend 7 functionType) [] 2 9
      .unit .unit functionType [] [] (.bind 5 (.resume 9 .unit) (.variable 7)) held false (some []) := by
    intro held
    apply Offer.available (fun _ => rfl) (fun _ => rfl)
    intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
    have known : (contracts.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
    have operand : Expression operations policy (contracts.insert owner contract) [] [] (.ticket 9 owner)
        ((Environment.empty.extend 7 functionType).extend 2 .unit) .unit contract.input [] (.request [] []) := inputSame.symm ▸ .stable .unit
    have resumed := Expression.resume (binder := 9) known (by simp [Execution.Scope.resolve]) (by rfl) operand
      (resumeSame.symm ▸ List.Subset.refl [])
      (answerSame.symm ▸ (by simp [ScopedPorts.InWorld, functionType, Value.port, ScopedPorts.Port.resources]))
    exact .typed (Expression.bind resumed (.stable (.variable (by simp [Environment.extend])
      (by simp [ScopedPorts.InWorld, functionType, Value.port, ScopedPorts.Port.resources])))) ClauseRowAdmission.resume_then_value_rows
  exact .cons operation_known (family false) (family true) .nil

/-- A replacement actually used in a clause becomes its returned function.
    The resulting function still carries the declaration of its inner handler. -/
theorem substituted_clause_retains_inner_handler :
    Declarations operations policy contracts [] Environment.empty [] effect functionType
      SourceClauseDeclarations.Examples.clauses table := by
  have changed := declarations_substitution variable_declaration function_value function_closed
  simpa [variableClauses, SourceClauseDeclarations.Examples.clauses, SourceClauseDeclarations.Examples.body,
    Clauses.subst, Code.subst] using changed

theorem clause_parameter_shadows_outer_binding :
    Declarations operations policy contracts [] Environment.empty [] effect functionType
      SourceClauseDeclarations.Examples.clauses SourceClauseDeclarations.Examples.table := by
  have changed := declarations_substitution
    (DeclaredSources.Examples.nested_declaration contracts (Environment.empty.extend 2 functionType)) function_value function_closed
  simpa only [SourceClauseDeclarations.Examples.clauses, Clauses.subst, ↓reduceIte] using changed

theorem beta_retains_handler_body :
    ∃ demand, ∃ requirements : Requirements demand,
      RawStep ⟨.app function .unit, .none, .nil⟩ ⟨SourceCallableExamples.body, .none, .nil⟩ [] [] ∧
      Expression operations policy contracts [] [] .none Environment.empty SourceCallableExamples.body .unit demand requirements ∧
      RecursiveOutward.Outward requirements (some []) := by
  have reduced := beta_source (stack := .nil)
    (DeclaredSources.Examples.function_source contracts Environment.empty .none)
    (.summaryUnit) ScopedExecution.Examples.unit_closed (List.Subset.refl [])
  simpa only [function, functionType, SourceCallableExamples.body, SourceCallableExamples.clauses,
    Code.subst, Clauses.subst, ite_self] using reduced

end Examples

end Ash.OneShot.DeclaredSourceSubstitution
#print axioms Ash.OneShot.DeclaredSourceSubstitution.legacy_substitution

#print axioms Ash.OneShot.DeclaredSourceSubstitution.substitution_at
#print axioms Ash.OneShot.DeclaredSourceSubstitution.substitution
#print axioms Ash.OneShot.DeclaredSourceSubstitution.callable_substitution

#print axioms Ash.OneShot.DeclaredSourceSubstitution.body_substitution
#print axioms Ash.OneShot.DeclaredSourceSubstitution.offer_substitution
#print axioms Ash.OneShot.DeclaredSourceSubstitution.declarations_substitution
#print axioms Ash.OneShot.DeclaredSourceSubstitution.selected_payload
#print axioms Ash.OneShot.DeclaredSourceSubstitution.beta_body
#print axioms Ash.OneShot.DeclaredSourceSubstitution.beta_source
#print axioms Ash.OneShot.DeclaredSourceSubstitution.Examples.function_value
#print axioms Ash.OneShot.DeclaredSourceSubstitution.Examples.function_closed
#print axioms Ash.OneShot.DeclaredSourceSubstitution.Examples.substituted_stable_application
#print axioms Ash.OneShot.DeclaredSourceSubstitution.Examples.variable_declaration
#print axioms Ash.OneShot.DeclaredSourceSubstitution.Examples.substituted_clause_retains_inner_handler
#print axioms Ash.OneShot.DeclaredSourceSubstitution.Examples.clause_parameter_shadows_outer_binding
#print axioms Ash.OneShot.DeclaredSourceSubstitution.Examples.beta_retains_handler_body
