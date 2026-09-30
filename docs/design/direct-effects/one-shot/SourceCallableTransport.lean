import SourceTemplates

/-!
Environment transport for the shared callable source evidence. The proof reuses
dependency agreement, port transport and fresh-resource dependency bounds.
-/
namespace Ash.OneShot.SourceCallableTransport
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts
open SourceTemplates (Expression CallableSummary ValueSummary)

theorem opened_environment_agree {code : Code}
    (agree : AgreeOn source destination code.dependencies) :
    AgreeOn source destination
      (code.instantiate (Instantiation.Environment.empty.bind binder identity)).dependencies := by
  intro name member
  rcases List.mem_append.mp (ScopedExpressions.acquisition_dependency_bound _ identity _ member) with original | introduced
  · exact agree name original
  · simp at introduced

theorem expression_environment_congr
    (source : Expression operations policy contracts world allowed scope environment code result demand requirements)
    (agree : AgreeOn environment destination code.dependencies) :
    Expression operations policy contracts world allowed scope destination code result demand requirements := by
  induction source using Expression.rec
      (motive_2 := fun world environment allowed code value row _ => ∀ destination,
        AgreeOn environment destination code.dependencies →
          CallableSummary operations policy contracts world destination allowed code value row)
      generalizing destination with
  | stable summary => exact .stable (CoherentSourceTypes.environment_congr summary agree)
  | callable summary ih => exact .callable (ih destination agree)
  | lambda body outward formed ih => exact .lambda (ih (agree_extend agree)) outward formed
  | purePair left right ihLeft ihRight => exact .purePair (ihLeft (agree_left agree)) (ihRight (agree_right agree))
  | pair left right ihLeft ihRight => exact .pair (ihLeft (agree_left agree)) (ihRight (agree_right agree))
  | app function argument admitted ihFunction ihArgument =>
      exact .app (ihFunction (agree_left agree)) (ihArgument (agree_right agree)) admitted
  | bind initializer body ihInit ihBody => exact .bind (ihInit (agree_left agree)) (ihBody (agree_extend (agree_right agree)))
  | branch condition yes no same ihCondition ihYes ihNo =>
      exact .branch (ihCondition (agree_left (agree_left agree)))
        (ihYes (agree_right (agree_left agree))) (ihNo (agree_right agree)) same
  | perform known admitted operand formed ih => exact .perform known admitted (ih (agree_right agree)) formed
  | handler body clauses capabilities coverage unique admitted table modes ih =>
      apply Expression.handler (ih (agree_right (agree_left agree))) _ capabilities coverage unique admitted table modes
      apply ScopedPorts.clauses_environment_congr clauses
      intro name member
      simp only [Environment.ports, agree_right agree name member]
  | resume known resolved permission operand admitted formed ih =>
      exact .resume known resolved permission (ih (fun name member => agree name (List.mem_cons_of_mem _ member))) admitted formed
  | discard known resolved permission unprotected admitted => exact .discard known resolved permission unprotected admitted
  | cleanup callback body admitted ihCallback ihBody =>
      exact .cleanup (ihCallback (agree_left agree)) (ihBody (agree_right agree)) admitted
  | resource initializer body formed effectsBound admitted outward ihInit ihBody =>
      exact .resource (ihInit (agree_left agree))
        (fun identity fresh => ihBody identity fresh destination
          (opened_environment_agree (agree_right agree))) formed effectsBound admitted outward
  | scopedResource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      exact .scopedResource (ihInit (agree_left agree))
        (fun identity fresh => ihBody identity fresh (opened_environment_agree (agree_right agree)))
        formed effectsBound admitted hidden
  | summaryUnit => exact .summaryUnit
  | summaryBoolean => exact .summaryBoolean
  | summaryInteger => exact .summaryInteger
  | summaryReference issued => exact .summaryReference issued
  | summaryVariable known formed =>
      rename_i destination agree
      exact .summaryVariable ((agree _ List.mem_cons_self).symm.trans known) formed
  | summaryPair left right ihLeft ihRight =>
      rename_i destination agree
      exact .summaryPair (ihLeft destination (agree_left agree)) (ihRight destination (agree_right agree))
  | summaryLambda body outward formed ih =>
      rename_i destination agree
      exact .summaryLambda (ih (agree_extend agree)) outward formed
  | summaryApp function argument admitted ihFunction ihArgument =>
      rename_i destination agree
      exact .summaryApp (ihFunction destination (agree_left agree)) (ihArgument destination (agree_right agree)) admitted
  | summaryBind initializer body ihInit ihBody =>
      rename_i destination agree
      exact .summaryBind (ihInit destination (agree_left agree)) (ihBody _ (agree_extend (agree_right agree)))
  | summaryBranch condition yes no ihCondition ihYes ihNo =>
      rename_i destination agree
      exact .summaryBranch (ihCondition destination (agree_left (agree_left agree)))
        (ihYes destination (agree_right (agree_left agree))) (ihNo destination (agree_right agree))
  | summaryPerform known admitted operand formed ih =>
      rename_i destination agree
      exact .summaryPerform known admitted (ih destination (agree_right agree)) formed
  | summaryCleanup callback body admitted ihCallback ihBody =>
      rename_i destination agree
      exact .summaryCleanup (ihCallback destination (agree_left agree)) (ihBody destination (agree_right agree)) admitted
  | summaryResource initializer body formed effectsBound admitted outward ihInit ihBody =>
      rename_i destination agree
      exact .summaryResource (ihInit destination (agree_left agree))
        (fun identity fresh => ihBody identity fresh destination (opened_environment_agree (agree_right agree)))
        formed effectsBound admitted outward

theorem callable_environment_congr
    (source : CallableSummary operations policy contracts world environment allowed code value row)
    (agree : AgreeOn environment destination code.dependencies) :
    CallableSummary operations policy contracts world destination allowed code value row :=
  CallableSources.environment_congr source
    (fun _ _ _ _ _ _ _ _ body known => expression_environment_congr body known) agree

theorem value_environment_congr
    (source : ValueSummary operations policy contracts world environment allowed code value)
    (agree : AgreeOn environment destination code.dependencies) :
    ValueSummary operations policy contracts world destination allowed code value := by
  induction source generalizing destination with
  | stable summary => exact .stable (CoherentSourceTypes.environment_congr summary agree)
  | callable summary => exact .callable (callable_environment_congr summary agree)
  | pair left right ihLeft ihRight => exact .pair (ihLeft (agree_left agree)) (ihRight (agree_right agree))
  | lambda body outward formed => exact .lambda (expression_environment_congr body (agree_extend agree)) outward formed

theorem closed_value_environment
    (source : ValueSummary operations policy contracts world environment allowed code value)
    (closed : ClosedValue code) (destination : Environment) :
    ValueSummary operations policy contracts world destination allowed code value :=
  value_environment_congr source (fun _ member => False.elim (ScopedTyping.closedValue_no_variable closed member))

theorem value_callable
    (source : ValueSummary operations policy contracts world environment allowed code value) :
    CallableSummary operations policy contracts world environment allowed code value [] := by
  induction source with
  | stable summary => exact CallableSources.from_legacy summary (fun _ _ _ _ _ _ checked => .stable checked)
  | callable summary => exact summary
  | pair left right ihLeft ihRight => exact .summaryPair ihLeft ihRight
  | lambda body outward formed => exact .summaryLambda body outward formed

theorem expression_empty_usage
    (source : Expression operations policy contracts world allowed scope environment code result demand requirements)
    (empty : scope = .none) : ScopedExpressions.Uses policy .none .available code .available := by
  induction source using Expression.rec
      (motive_2 := fun _ _ _ code _ _ _ => ScopedExpressions.Uses policy .none .available code .available) with
  | stable summary => exact ClauseProtection.stable_usage (CoherentSourceTypes.protection_summary summary) policy .none .available
  | callable summary ih => exact ih
  | lambda body outward formed ih => exact .lambda (ih rfl)
  | purePair left right ihLeft ihRight | pair left right ihLeft ihRight => exact .pair (ihLeft empty) (ihRight empty)
  | app function argument admitted ihFunction ihArgument => exact .app (ihFunction empty) (ihArgument empty)
  | bind initializer body ihInit ihBody => exact .bind (ihInit empty) (ihBody empty)
  | branch condition yes no same ihCondition ihYes ihNo => exact .branch (ihCondition empty) (ihYes empty) (ihNo empty)
  | perform known admitted operand formed ih => exact .perform (ih empty)
  | handler body clauses capabilities coverage unique admitted table modes ih => exact .handle (ih empty) capabilities
  | resume known resolved permission operand admitted formed ih | discard known resolved permission unprotected admitted =>
      subst_vars
      cases resolved
  | cleanup callback body admitted ihCallback ihBody => exact .cleanup (ihCallback empty) (ihBody empty)
  | resource initializer body formed effectsBound admitted outward ihInit ihBody =>
      obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
      exact .resource (ihInit empty) ((instantiation_preserves_usage_iff _ _).mp (ihBody identity fresh))
  | scopedResource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
      exact .resource (ihInit empty) ((instantiation_preserves_usage_iff _ _).mp (ihBody identity fresh empty))
  | summaryUnit => exact .unit
  | summaryBoolean => exact .boolean
  | summaryInteger => exact .integer
  | summaryReference issued => exact .resourceRef
  | summaryVariable known formed => exact .variable
  | summaryPair left right ihLeft ihRight => exact .pair ihLeft ihRight
  | summaryLambda body outward formed ih => exact .lambda (ih rfl)
  | summaryApp function argument admitted ihFunction ihArgument => exact .app ihFunction ihArgument
  | summaryBind initializer body ihInit ihBody => exact .bind ihInit ihBody
  | summaryBranch condition yes no ihCondition ihYes ihNo => exact .branch ihCondition ihYes ihNo
  | summaryPerform known admitted operand formed ih => exact .perform ih
  | summaryCleanup callback body admitted ihCallback ihBody => exact .cleanup ihCallback ihBody
  | summaryResource initializer body formed effectsBound admitted outward ihInit ihBody =>
      obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
      exact .resource ihInit ((instantiation_preserves_usage_iff _ _).mp (ihBody identity fresh))

theorem value_usage
    (source : ValueSummary operations policy contracts world environment allowed code value) :
    ScopedExpressions.Uses policy .none .available code .available :=
  expression_empty_usage (source.expression .none) rfl

theorem expression_allowed_mono
    (source : Expression operations policy contracts world allowed scope environment code result demand requirements)
    (more : allowed ⊆ destination) :
    Expression operations policy contracts world destination scope environment code result demand requirements := by
  induction source using Expression.rec (motive_2 := fun _ _ _ _ _ _ _ => True) generalizing destination with
  | stable summary => exact .stable (CoherentSourceTypes.allowed_mono summary more)
  | callable summary ih => exact .callable (CallableSources.allowed_mono summary more)
  | lambda body outward formed ih => exact .lambda body outward formed
  | purePair left right ihLeft ihRight => exact .purePair (ihLeft more) (ihRight more)
  | pair left right ihLeft ihRight => exact .pair (ihLeft more) (ihRight more)
  | app function argument admitted ihFunction ihArgument => exact .app (ihFunction more) (ihArgument more) (admitted.trans more)
  | bind initializer body ihInit ihBody => exact .bind (ihInit more) (ihBody more)
  | branch condition yes no same ihCondition ihYes ihNo => exact .branch (ihCondition more) (ihYes more) (ihNo more) same
  | perform known admitted operand formed ih => exact .perform known (more admitted) (ih more) formed
  | handler body clauses capabilities coverage unique admitted table modes ih =>
      exact .handler body clauses capabilities coverage unique (admitted.trans more) table modes
  | resume known resolved permission operand admitted formed ih => exact .resume known resolved permission (ih more) (admitted.trans more) formed
  | discard known resolved permission unprotected admitted => exact .discard known resolved permission unprotected (admitted.trans more)
  | cleanup callback body admitted ihCallback ihBody => exact .cleanup (ihCallback more) (ihBody more) (admitted.trans more)
  | resource initializer body formed effectsBound admitted outward ihInit ihBody =>
      exact .resource (ihInit more) body formed effectsBound (admitted.trans more) outward
  | scopedResource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      exact .scopedResource (ihInit more) body formed effectsBound (admitted.trans more) hidden
  | _ => intros; trivial

theorem lambda_body
    (source : ValueSummary operations policy contracts world environment allowed
      (.lambda parameter code) (.function input output requests latent)) :
    ∃ demand requirements,
      Expression operations policy contracts world requests .none (environment.extend parameter input)
        code output demand requirements ∧ RecursiveOutward.Outward requirements (some latent) := by
  have summary := value_callable source
  cases summary with
  | summaryLambda body outward formed => exact ⟨_, _, body, outward⟩

end Ash.OneShot.SourceCallableTransport
#print axioms Ash.OneShot.SourceCallableTransport.opened_environment_agree
#print axioms Ash.OneShot.SourceCallableTransport.expression_environment_congr
#print axioms Ash.OneShot.SourceCallableTransport.callable_environment_congr
#print axioms Ash.OneShot.SourceCallableTransport.value_environment_congr
#print axioms Ash.OneShot.SourceCallableTransport.closed_value_environment
#print axioms Ash.OneShot.SourceCallableTransport.value_callable
#print axioms Ash.OneShot.SourceCallableTransport.expression_empty_usage
#print axioms Ash.OneShot.SourceCallableTransport.value_usage
#print axioms Ash.OneShot.SourceCallableTransport.expression_allowed_mono
#print axioms Ash.OneShot.SourceCallableTransport.lambda_body
