import SourceAnnotatedValues

/-! Closed substitution retains finite source annotations and the existing
rich source choices. Erased clause checks and resource-opening transport reuse
the established substitution laws. -/
namespace Ash.OneShot.SourceAnnotatedCode
open Instantiation

/-- Reuse the instantiation/closure equivalence rather than introduce another
free-name induction for substitution. -/
theorem Term.substitution_closed {term value : Term} (name : Nat)
    (sourceClosed : term.ResourceClosed) (valueClosed : value.ResourceClosed) :
    (term.subst name value).ResourceClosed := by
  let allNames : Environment := fun _ => some 0
  have resolved := ((term.subst name value).instantiation_closes_iff allNames).mpr (fun _ _ => ⟨0, rfl⟩)
  rw [term.instantiation_subst name value allNames valueClosed,
    term.closed_instantiation_identity allNames sourceClosed] at resolved
  exact resolved

end Ash.OneShot.SourceAnnotatedCode

namespace Ash.OneShot.SourceAnnotatedSources
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceAnnotatedCode (Term)
open RecursiveRequirements (Requirements)
open SourcePlannedTyping (Value Environment Operations Contract Contracts insert_extends)
open SourcePlanSignatures (clauseSignatures)
open SourceDeclarationPlans (ClausePlans)

theorem Expression.node_checked
    (source : Expression operations policy contracts world allowed scope environment code result demand requirements checking) :
    Node operations policy contracts world allowed scope environment code result demand requirements checking := by
  cases source with | checked hint closed node => exact node

/-- Only a replaced variable changes the root hint. Its environment lookup
identifies the very input type authenticated by the replacement's hint. -/
theorem substitution_hint {environment : Environment} {value : Term}
    (source : Expression operations policy contracts world allowed scope (environment.extend name input) code result demand requirements checking)
    (replacement : SourceFocusHints.checkSource Instantiation.Environment.empty value.hint input = true) :
    SourceFocusHints.checkSource Instantiation.Environment.empty (code.subst name value).hint result = true := by
  cases source with
  | checked hint closed node => cases node with
    | «variable» known formed =>
        simp only [Term.subst]
        split
        · rename_i same
          subst name
          simp only [Environment.extend, ↓reduceIte] at known
          cases Option.some.inj known
          exact replacement
        · exact hint
    | unit | boolean | integer | reference | lambda | purePair | pair | app | bind | branch
      | perform | handler | resume | discard | cleanup | resource => exact hint

/-- Retarget the original clause witnesses to the substituted annotated bodies.
Mode plans remain unchanged, exactly as in the existing raw substitution. -/
def substitutePlans (clauses : SourceAnnotatedCode.Clauses) (plans : ClausePlans clauses.erase families)
    (name : Nat) (value : Term) : ClausePlans (clauses.subst name value).erase families := by
  cases clauses with
  | nil => cases plans; exact .nil
  | cons operation parameter binder body rest =>
      cases plans with
      | cons ordinary protectedMode restPlan =>
          exact .cons ordinary protectedMode (substitutePlans rest restPlan name value)
termination_by structural clauses

theorem substitutePlans_signature (clauses : SourceAnnotatedCode.Clauses) (plans : ClausePlans clauses.erase families)
    (isValue : value.erase.IsValue) :
    clauseSignatures (substitutePlans clauses plans name value) = clauseSignatures plans := by
  cases clauses with
  | nil => cases plans; rfl
  | cons operation parameter binder body rest =>
      cases plans with
      | cons ordinary protectedMode restPlan =>
          change SourcePlanSignatures.ClauseSignatures.cons
              (if name = parameter then body else body.subst name value).erase.requiredActions
              (SourcePlanSignatures.modeSignatures ordinary) (SourcePlanSignatures.modeSignatures protectedMode)
              (clauseSignatures (substitutePlans rest restPlan name value)) =
            .cons body.erase.requiredActions (SourcePlanSignatures.modeSignatures ordinary)
              (SourcePlanSignatures.modeSignatures protectedMode) (clauseSignatures restPlan)
          split <;> simp only [Term.erase_subst, Code.substitution_required_actions _ _ isValue,
            substitutePlans_signature rest restPlan isValue]
termination_by structural clauses

theorem substitution_at
    (source : Expression operations policy contracts world allowed scope sourceEnvironment code result demand requirements dependencies) :
    ∀ environment name input value, sourceEnvironment = environment.extend name input →
      ValueSummary operations policy contracts world environment allowed value input → ClosedValue value.erase →
      Expression operations policy contracts world allowed scope environment (code.subst name value) result demand requirements dependencies := by
  induction source using Expression.rec
      (motive_2 := fun contracts world allowed scope sourceEnvironment code result demand requirements _ checking _ =>
        ∀ environment name input value, sourceEnvironment = environment.extend name input →
          ValueSummary operations policy contracts world environment allowed value input → ClosedValue value.erase →
          Node operations policy contracts world allowed scope environment (code.subst name value) result demand requirements checking)
      (motive_3 := fun contracts world allowed scope sourceEnvironment code result header _ dependencies _ =>
        ∀ environment name input value, sourceEnvironment = environment.extend name input →
          ValueSummary operations policy contracts world environment allowed value input → ClosedValue value.erase →
          Body operations policy contracts world allowed scope environment (code.subst name value) result header dependencies)
      (motive_4 := fun contracts world sourceEnvironment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row _ dependencies _ =>
        ∀ environment name valueType value, sourceEnvironment = environment.extend name valueType →
          ValueSummary operations policy contracts world environment allowed value valueType → ClosedValue value.erase →
          Offer operations policy contracts world environment allowed parameter binder argument input answer resumeEffects closeEffects
            (if name = parameter then code else code.subst name value) held disposes row dependencies)
      (motive_5 := fun contracts world sourceEnvironment allowed effect answer clauses table _ dependencies _ =>
        ∀ environment name input value, sourceEnvironment = environment.extend name input →
          ValueSummary operations policy contracts world environment allowed value input → ClosedValue value.erase →
          Declarations operations policy contracts world environment allowed effect answer (clauses.subst name value) table (substitutePlans clauses dependencies name value)) with
  | checked hint closed node ih =>
      intro environment name input value environmentSame replacement valueClosed
      cases environmentSame
      have original := Expression.checked hint closed node
      exact .checked (substitution_hint original replacement.hint_checked)
        (SourceAnnotatedCode.Term.check_closed_iff.mpr
          (Term.substitution_closed name original.resource_closed replacement.resource_closed))
        (ih environment name input value rfl replacement valueClosed)
  | unit | boolean | integer | reference =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      first | exact .unit | exact .boolean | exact .integer | apply Node.reference; assumption
  | «variable» known formed =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      simp only [Term.subst]
      split
      · rename_i same
        subst name
        simp only [Environment.extend, ↓reduceIte] at known
        cases Option.some.inj known
        exact (Values.change_context replacement closed.1 _ _).node_checked
      · rename_i different
        exact .variable (by simpa [Environment.extend, Ne.symm different] using known) formed
  | lambda body outward formed latentBound ih =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      simp only [Term.subst]
      apply Node.lambda _ outward formed latentBound
      split
      · rename_i same
        subst name
        simpa only [Environment.extend_shadow] using body
      · rename_i different
        exact ih _ name input value (Environment.extend_commute environment name _ input _ different)
          (Values.change_allowed (Values.closed_environment replacement closed _) closed.1 _) closed
  | purePair left right ihLeft ihRight =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      exact .purePair (ihLeft environment name input value rfl replacement closed) (ihRight environment name input value rfl replacement closed)
  | pair left right ihLeft ihRight =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      exact .pair (ihLeft environment name input value rfl replacement closed) (ihRight environment name input value rfl replacement closed)
  | app function argument admitted ihFunction ihArgument =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      exact .app (ihFunction environment name input value rfl replacement closed) (ihArgument environment name input value rfl replacement closed) admitted
  | bind initializer body ihInit ihBody =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      apply Node.bind (ihInit environment name input value rfl replacement closed)
      split
      · rename_i same
        subst name
        simpa only [Environment.extend_shadow] using body
      · rename_i different
        exact ihBody _ name input value (Environment.extend_commute environment name _ input _ different)
          (Values.closed_environment replacement closed _) closed
  | branch condition yes no same ihCondition ihYes ihNo =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      exact .branch (ihCondition environment name input value rfl replacement closed) (ihYes environment name input value rfl replacement closed) (ihNo environment name input value rfl replacement closed) same
  | perform known admitted operand formed ih =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      exact .perform known admitted (ih environment name input value rfl replacement closed) formed
  | handler body clauses capabilities coverage unique admitted table modes declarations ihBody ihDecl =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      have changed := ScopedPorts.clauses_typed_substitution
        (by simpa only [SourcePlannedTyping.environment_erase_extend, SourceDependencyAnnotations.environment_erase_extend, CoherentSourceTypes.ports_extend] using clauses)
        ((Values.erase (Values.change_allowed replacement closed.1 []) closed.1).ports .none) closed
      have changedUsage := ScopedExpressions.clauses_usage_substitution capabilities closed.1
        (SourceCallableTransport.value_usage (Values.erase replacement closed.1)) name
      simp only [Term.subst]
      rw [← substitutePlans_signature _ _ (name := name) closed.1]
      exact .handler
        (ihBody environment name input value rfl (Values.change_allowed replacement closed.1 _) closed)
        (by simpa only [SourceAnnotatedCode.Clauses.erase_subst] using changed)
        (by simpa only [SourceAnnotatedCode.Clauses.erase_subst] using changedUsage)
        (by simpa only [SourceAnnotatedCode.Clauses.erase_subst, ScopedPorts.Covers, ScopedTyping.clause_keys_substitution] using coverage)
        (by simpa only [SourceAnnotatedCode.Clauses.erase_subst, ScopedTyping.clause_keys_substitution] using unique) admitted table
        (by simpa only [SourceAnnotatedCode.Clauses.erase_subst] using SourceTemplates.clause_modes_substitution modes closed.1 name)
        (ihDecl environment name input value rfl (Values.change_allowed replacement closed.1 _) closed)
  | resume known resolved permission operand admitted formed ih =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      exact .resume known resolved permission (ih environment name input value rfl replacement closed) admitted formed
  | discard known resolved permission unprotected admitted =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      exact .discard known resolved permission unprotected admitted
  | cleanup callback body admitted ihCallback ihBody =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      exact .cleanup (ihCallback environment name input value rfl replacement closed) (ihBody environment name input value rfl replacement closed) admitted
  | resource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      rename_i environment name input value environmentSame replacement closed
      cases environmentSame
      apply Node.resource (ihInit environment name input value rfl replacement closed) _ formed effectsBound admitted hidden
      intro identity fresh
      rw [Term.instantiation_subst _ name value _ replacement.resource_closed]
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
        (by split <;> simpa only [Term.erase_subst, Code.substitution_required_actions _ _ closed.1] using resumeInterface)
        (by split <;> simpa only [Term.erase_subst, Code.substitution_required_actions _ _ closed.1] using closeInterface)
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
    (replacement : ValueSummary operations policy contracts world environment allowed value input) (closed : ClosedValue value.erase) :
    Expression operations policy contracts world allowed scope environment (code.subst name value) result demand requirements dependencies :=
  substitution_at source environment name input value rfl replacement closed

end Ash.OneShot.SourceAnnotatedSources

#print axioms Ash.OneShot.SourceAnnotatedCode.Term.substitution_closed
#print axioms Ash.OneShot.SourceAnnotatedSources.Expression.node_checked
#print axioms Ash.OneShot.SourceAnnotatedSources.substitution_hint
#print axioms Ash.OneShot.SourceAnnotatedSources.substitutePlans_signature
#print axioms Ash.OneShot.SourceAnnotatedSources.substitution_at
#print axioms Ash.OneShot.SourceAnnotatedSources.substitution
