import SourceAnnotatedSources

/-! Structural focus decomposition retains the same annotated child types as
source checking. The old context, requirement evaluation and value-summary
proofs are reused through erasure; no successor validity is assumed. -/
namespace Ash.OneShot.SourceAnnotatedSources
open ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements evaluate)
open ProtectionResiduals (merge merge_assoc)
open OwnerPhaseTransitions (spendAll)
open RecursiveContexts (evaluate_request)
open SourceDependencyAnnotations (Dependencies)
open SourcePlannedTyping (Value Environment Operations Contract Contracts)
open SourcePlanSignatures (Signature)

inductive Context (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (world : List Nat) (environment : Environment) (allowed : List Instance) (scope : Execution.Scope) :
    SourceAnnotatedCode.Context → Value → Value → (demand : List Nat) → Requirements demand → {dependencies : Dependencies} → Signature dependencies → Prop where
  | pairLeft (right : Expression operations policy contracts world allowed scope environment code output demand requirements dependencies) :
      Context operations policy contracts world environment allowed scope (.pairLeft hint code) input (.pair input output) demand requirements dependencies
  | pairRight (left : Expression operations policy contracts world allowed scope environment code input demand requirements checking)
      (isValue : code.erase.IsValue) :
      Context operations policy contracts world environment allowed scope (.pairRight hint code) output (.pair input output) [] (.request [] []) .pure
  | appFunction (argument : Expression operations policy contracts world allowed scope environment code input demand requirements argumentDep)
      (admitted : requests ⊆ allowed) :
      Context operations policy contracts world environment allowed scope (.appFunction hint code) (.function input output requests latent bodyDep)
        output demand (.emitAfter requirements [] latent) (.sequence argumentDep bodyDep)
  | appArgument (function : Expression operations policy contracts world allowed scope environment code (.function input output requests latent bodyDep) demand requirements checking)
      (isValue : code.erase.IsValue)
      (admitted : requests ⊆ allowed) :
      Context operations policy contracts world environment allowed scope (.appArgument hint code) input output [] (.request [] latent) bodyDep
  | bind (body : Expression operations policy contracts world allowed scope (environment.extend parameter input) code output demand requirements dependencies) :
      Context operations policy contracts world environment allowed scope (.bind hint parameter code) input output demand requirements dependencies
  | branch (yesSource : Expression operations policy contracts world allowed scope environment a output yesDemand yes yesDep)
      (noSource : Expression operations policy contracts world allowed scope environment b output noDemand no noDep)
      (same : yesDemand.Perm noDemand) :
      Context operations policy contracts world environment allowed scope (.branch hint a b) .boolean output yesDemand (.choice yes no same) (.choice yesDep noDep)
  | perform (known : operations effect operation = some (input, output)) (admitted : effect ∈ allowed)
      (formed : ScopedPorts.InWorld world output.erase.erase.port) :
      Context operations policy contracts world environment allowed scope (.perform hint (Instantiation.freezeEffect effect) operation)
        input output [] (.request [] [⟨effect, operation, false⟩]) (.request (effect := effect) (operation := operation))
  | resume (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
      (permission : (policy binder).resume = true)
      (admitted : contract.resumeEffects ⊆ allowed) (formed : ScopedPorts.InWorld world contract.answer.erase.erase.port) :
      Context operations policy contracts world environment allowed scope (.resume hint binder) contract.input contract.answer
        (owner :: contract.resumeDemand) (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) (.invoke (key := ⟨owner, .resume⟩))
  | cleanup (body : Expression operations policy contracts world allowed scope environment code output demand requirements dependencies)
      (admitted : requests ⊆ allowed) :
      Context operations policy contracts world environment allowed scope (.cleanup hint code) (.function .unit .unit requests latent callbackDep)
        output demand (.emitAfter requirements [] (qualify true latent)) (.cleanup (needs := requests) callbackDep dependencies)
  | resource {bodyRequirements : Nat → Requirements demand} {bodyDependencies : Nat → Dependencies} {bodySignatures : ∀ identity, Signature (bodyDependencies identity)}
      (body : ∀ identity, identity ∉ world → Expression operations policy contracts (world ++ [identity])
        (.cell identity :: residual) scope environment
        (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output demand (bodyRequirements identity) (bodySignatures identity))
      (formed : ScopedPorts.InWorld world output.erase.erase.port)
      (effectsBound : residual.flatMap Instance.resources ⊆ world) (admitted : residual ⊆ allowed)
      (hidden : ∀ identity, identity ∉ world → ResourceRequirements.Hides identity (bodyRequirements identity) outward) :
      Context operations policy contracts world environment allowed scope (.resource hint binder code) .integer output demand outward (.resource bodySignatures)

theorem Context.erase
    (source : Context operations policy contracts world environment allowed scope position input output demand requirements checking) :
    SourcePlannedSources.Context operations policy contracts world environment allowed scope position.erase input output demand requirements checking := by
  cases source with
  | pairLeft right => exact .pairLeft right.erase
  | pairRight left isValue => exact .pairRight (SourcePlannedSources.value_summary left.erase isValue)
  | appFunction argument admitted => exact .appFunction argument.erase admitted
  | appArgument function isValue admitted => exact .appArgument (SourcePlannedSources.value_summary function.erase isValue) admitted
  | bind body => exact .bind body.erase
  | branch yes no same => exact .branch yes.erase no.erase same
  | perform known admitted formed => exact .perform known admitted formed
  | resume known resolved permission admitted formed => exact .resume known resolved permission admitted formed
  | cleanup body admitted => exact .cleanup body.erase admitted
  | resource body formed effectsBound admitted hidden =>
      exact .resource (fun identity fresh => by
        simpa only [SourceAnnotatedCode.Term.erase_instantiate] using (body identity fresh).erase)
        formed effectsBound admitted hidden

theorem focus_decompose
    (source : Expression operations policy contracts world allowed scope environment whole output demand requirements checking)
    (focus : SourceAnnotatedCode.Focus whole child position) :
    ∃ (input : Value) (childDemand restDemand : List Nat) (current : Requirements childDemand) (rest : Requirements restDemand)
      (childDependencies restDependencies : Dependencies) (childSignature : Signature childDependencies) (restSignature : Signature restDependencies),
      Expression operations policy contracts world allowed scope environment child input childDemand current childSignature ∧
      Context operations policy contracts world environment allowed scope position input output restDemand rest restSignature ∧
      SourcePlannedSources.FocusSignature checking childSignature restSignature ∧
      demand = childDemand ++ restDemand ∧
      ∀ store receiving before, RecursiveRequirements.evaluate store receiving before requirements =
        ProtectionResiduals.merge (RecursiveRequirements.evaluate store receiving before current)
          (RecursiveRequirements.evaluate store receiving (OwnerPhaseTransitions.spendAll before childDemand) rest) := by
  cases source with
  | checked hint closed node => cases node with
    | handler => cases focus
    | unit | boolean | integer | reference | «variable» => cases focus
    | lambda => cases focus
    | purePair left right => cases focus with
      | pairLeft =>
          refine ⟨_, [], [], _, _, _, _, _, _, left, .pairLeft right, .pure, rfl, ?_⟩
          intro store receiving before
          simp only [RecursiveRecomposition.evaluate_empty, merge, List.nil_append]
      | pairRight isValue notValue =>
          refine ⟨_, [], [], _, _, _, _, _, _, right, .pairRight left isValue, .pure, rfl, ?_⟩
          intro store receiving before
          simp only [RecursiveRecomposition.evaluate_empty, merge, List.nil_append]
    | pair left right => cases focus with
      | pairLeft => exact ⟨_, _, _, _, _, _, _, _, _, left, .pairLeft right, .sequence, rfl, fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
      | pairRight isValue notValue =>
          have empty := SourceTemplates.expression_value_demand (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase left.erase))) isValue
          subst_vars
          refine ⟨_, _, [], _, _, _, _, _, _, right, .pairRight left isValue, .pairRight, by simp, ?_⟩
          intro store receiving before
          simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase left.erase))) isValue,
            RecursiveRecomposition.evaluate_empty, spendAll, RecursiveRecomposition.merge_empty_left, RecursiveRecomposition.merge_empty_right]
    | app function argument admitted => cases focus with
      | appFunction =>
          refine ⟨_, _, _, _, _, _, _, _, _, function, .appFunction argument admitted, .sequence, rfl, ?_⟩
          intro store receiving before
          simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence, PhaseRechecking.spendAll_append, merge_assoc]
      | appArgument isValue notValue =>
          have empty := SourceTemplates.expression_value_demand (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase function.erase))) isValue
          subst_vars
          refine ⟨_, _, [], _, _, _, _, _, _, argument, .appArgument function isValue admitted, .appArgument, by simp, ?_⟩
          intro store receiving before
          simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence,
            RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase function.erase))) isValue, spendAll, List.nil_append,
            RecursiveRecomposition.merge_empty_left, evaluate_request]
    | bind initializer body => cases focus with
      | bind => exact ⟨_, _, _, _, _, _, _, _, _, initializer, .bind body, .sequence, rfl, fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
    | branch condition yes no same => cases focus with
      | branch => exact ⟨_, _, _, _, _, _, _, _, _, condition, .branch yes no same, .sequence, rfl, fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
    | perform known admitted operand formed => cases focus with
      | perform =>
          refine ⟨_, _, [], _, _, _, _, _, _, operand, .perform known admitted formed, .sequence, by simp, ?_⟩
          intro store receiving before
          simp only [RecursiveRequirements.evaluate_emit, evaluate_request, List.nil_append]
    | resource initializer body formed effectsBound admitted hidden => cases focus with
      | resource notValue =>
          exact ⟨_, _, _, _, _, _, _, _, _, initializer, .resource body formed effectsBound admitted hidden,
            .sequence, rfl, fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
    | resume known resolved permission operand admitted formed => cases focus with
      | resume => exact ⟨_, _, _, _, _, _, _, _, _, operand, .resume known resolved permission admitted formed, .sequence, rfl,
          fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
    | discard => cases focus
    | cleanup callback body admitted => cases focus with
      | cleanup =>
          refine ⟨_, _, _, _, _, _, _, _, _, callback, .cleanup body admitted, .sequence, rfl, ?_⟩
          intro store receiving before
          simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence, PhaseRechecking.spendAll_append, merge_assoc]

/-- Source decomposition authenticates the very child whose finite hint the
runtime frame guard reads, including application, bind and cleanup positions. -/
theorem focus_frame_ports
    (source : Expression operations policy contracts world allowed scope environment whole output demand requirements checking)
    (focus : SourceAnnotatedCode.Focus whole child position)
    (guard : SourceAnnotatedCode.checkFocusFrame Instantiation.Environment.empty child result stack plain = true) :
    ∃ (input : Value) (childDemand : List Nat) (current : Requirements childDemand)
      (childDependencies : Dependencies) (childSignature : Signature childDependencies),
      Expression operations policy contracts world allowed scope environment child input childDemand current childSignature ∧
      ScopedPorts.eraseType plain.input = input.erase.erase.port ∧
      ScopedPorts.eraseType plain.output = SourceScheduledExecution.stackInputPort stack result := by
  obtain ⟨input, childDemand, restDemand, current, rest, childDependencies, restDependencies,
    childSignature, restSignature, childSource, context, split, same, evaluation⟩ := focus_decompose source focus
  exact ⟨input, childDemand, current, childDependencies, childSignature, childSource,
    SourceFocusHints.source_frame_agreement childSource.hint_checked guard⟩

/-- The existing frame constructor also produces a successful finite guard.
This theorem retains the annotated child and context; it does not yet preserve
those annotations through arbitrary runtime execution. -/
theorem focus_prepare
    (source : Expression operations policy contracts world allowed scope (fun _ => none) whole output demand requirements checking)
    (focus : SourceAnnotatedCode.Focus whole child position)
    (scopeTyped : ScopedPorts.EffectScope contracts.erase.erase.ports scope ticket)
    (answer : output.erase.erase.port = SourceScheduledExecution.stackInputPort stack result) :
    ∃ (input : Value) (childDemand restDemand : List Nat) (current : Requirements childDemand) (rest : Requirements restDemand)
      (childDependencies restDependencies : Dependencies) (childSignature : Signature childDependencies) (restSignature : Signature restDependencies)
      (plain : PlainData),
      Expression operations policy contracts world allowed scope (fun _ => none) child input childDemand current childSignature ∧
      Context operations policy contracts world (fun _ => none) allowed scope position input output restDemand rest restSignature ∧
      plain.context = position.erase ∧ plain.scope = scope ∧
      SourceDependencyFrames.Frame operations.erase policy contracts.erase tables families world (.plain plain)
        input.erase output.erase restDemand rest (.plain restDependencies) allowed allowed ∧
      RawStep ⟨whole.erase, scope, stack⟩ ⟨child.erase, scope, .push (.plain plain) stack⟩ [] [] ∧
      SourceAnnotatedCode.checkFocusFrame Instantiation.Environment.empty child result stack plain = true ∧
      SourceFocusHints.checkSource Instantiation.Environment.empty position.hint output = true ∧
      SourcePlannedSources.FocusSignature checking childSignature restSignature ∧
      demand = childDemand ++ restDemand ∧
      (∀ store receiving before, evaluate store receiving before requirements =
        merge (evaluate store receiving before current) (evaluate store receiving (spendAll before childDemand) rest)) := by
  obtain ⟨input, childDemand, restDemand, current, rest, childDependencies, restDependencies,
    childSignature, restSignature, childSource, context, split, same, evaluation⟩ := focus_decompose source focus
  obtain ⟨plain, contextSame, scopeSame, inputAnnotation, outputAnnotation⟩ := RecursiveContexts.prepare_plain
    (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase (SourcePlannedSources.expression_erase source.erase)))
    focus.erase scopeTyped input.erase.erase
  have synchronized : SourcePlannedSources.Context operations policy contracts world (fun _ => none) allowed plain.scope plain.context
      input output restDemand rest restSignature := by simpa only [contextSame, scopeSame] using context.erase
  refine ⟨input, childDemand, restDemand, current, rest, childDependencies, restDependencies,
    childSignature, restSignature, plain, childSource, context, contextSame, scopeSame,
    synchronized.plain_frame (by simpa only [scopeSame] using scopeTyped) inputAnnotation outputAnnotation,
    ?_, ?_, ?_, split, same, evaluation⟩
  · simpa only [scopeSame] using RawStep.focus plain (by simpa only [contextSame] using focus.erase) stack
  · change decide (_ ∧ _) = true
    apply decide_eq_true
    exact ⟨(SourceFocusHints.check_source_iff.mp childSource.hint_checked).trans (congrArg some inputAnnotation),
      outputAnnotation.symm.trans answer⟩
  · simpa only [focus.output_hint] using source.hint_checked

end Ash.OneShot.SourceAnnotatedSources

#print axioms Ash.OneShot.SourceAnnotatedSources.Context.erase
#print axioms Ash.OneShot.SourceAnnotatedSources.focus_decompose

#print axioms Ash.OneShot.SourceAnnotatedSources.focus_frame_ports
#print axioms Ash.OneShot.SourceAnnotatedSources.focus_prepare
