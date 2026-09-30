import SourcePlannedSources
import SourceDependencyFrames
import DeclaredSourceContexts

/-! Synchronized source types and signatures at actual evaluation positions.
The existing context and frame certificates are projections of the same choices.
Runtime-state preservation and capture admission remain separate connections. -/
namespace Ash.OneShot.SourcePlannedSources
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements evaluate)
open ProtectionResiduals (merge merge_assoc)
open OwnerPhaseTransitions (spendAll)
open RecursiveContexts (evaluate_request)
open SourceDependencyAnnotations (Dependencies)
open SourcePlannedTyping (Value Environment Operations Contract Contracts)
open SourcePlanSignatures (Signature)
open SourceScheduledCleanupInterfaces.Lexical.Recursive (annotateDisposals)

abbrev ValueSummary operations policy contracts world environment allowed code value :=
  Expression operations policy contracts world allowed .none environment code value [] (.request [] []) .pure

/-- Reuse the original body proof when a value changes its evaluation scope. -/
theorem value_change_scope
    (source : Expression operations policy contracts world allowed scope environment code value demand requirements checking)
    (isValue : code.IsValue) (next : Execution.Scope) :
    Expression operations policy contracts world allowed next environment code value demand requirements checking := by
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

theorem value_pure
    (source : Expression operations policy contracts world allowed scope environment code value demand requirements checking)
    (isValue : code.IsValue) : Expression operations policy contracts world allowed scope environment code value [] (.request [] []) .pure := by
  induction source using Expression.rec
    (motive_2 := fun _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ _ _ _ _ => True) with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | lambda body outward formed latentBound ih => exact .lambda body outward formed latentBound
  | purePair left right ihLeft ihRight | pair left right ihLeft ihRight => exact .purePair (ihLeft isValue.1) (ihRight isValue.2)
  | «variable» | app | bind | branch | perform | handler | resume | discard | cleanup | resource => cases isValue
  | typed | unavailable | available | nil | cons => trivial

theorem value_summary
    (source : Expression operations policy contracts world allowed scope environment code value demand requirements checking)
    (isValue : code.IsValue) : ValueSummary operations policy contracts world environment allowed code value :=
  value_change_scope (value_pure source isValue) isValue .none

inductive Context (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (world : List Nat) (environment : Environment) (allowed : List Instance) (scope : Execution.Scope) :
    ScopedExecution.Context → Value → Value → (demand : List Nat) → Requirements demand → {dependencies : Dependencies} → Signature dependencies → Prop where
  | pairLeft (right : Expression operations policy contracts world allowed scope environment code output demand requirements dependencies) :
      Context operations policy contracts world environment allowed scope (.pairLeft code) input (.pair input output) demand requirements dependencies
  | pairRight (left : ValueSummary operations policy contracts world environment allowed code input) :
      Context operations policy contracts world environment allowed scope (.pairRight code) output (.pair input output) [] (.request [] []) .pure
  | appFunction (argument : Expression operations policy contracts world allowed scope environment code input demand requirements argumentDep)
      (admitted : requests ⊆ allowed) :
      Context operations policy contracts world environment allowed scope (.appFunction code) (.function input output requests latent bodyDep)
        output demand (.emitAfter requirements [] latent) (.sequence argumentDep bodyDep)
  | appArgument (function : ValueSummary operations policy contracts world environment allowed code (.function input output requests latent bodyDep))
      (admitted : requests ⊆ allowed) :
      Context operations policy contracts world environment allowed scope (.appArgument code) input output [] (.request [] latent) bodyDep
  | bind (body : Expression operations policy contracts world allowed scope (environment.extend parameter input) code output demand requirements dependencies) :
      Context operations policy contracts world environment allowed scope (.bind parameter code) input output demand requirements dependencies
  | branch (yesSource : Expression operations policy contracts world allowed scope environment a output yesDemand yes yesDep)
      (noSource : Expression operations policy contracts world allowed scope environment b output noDemand no noDep)
      (same : yesDemand.Perm noDemand) :
      Context operations policy contracts world environment allowed scope (.branch a b) .boolean output yesDemand (.choice yes no same) (.choice yesDep noDep)
  | perform (known : operations effect operation = some (input, output)) (admitted : effect ∈ allowed)
      (formed : ScopedPorts.InWorld world output.erase.erase.port) :
      Context operations policy contracts world environment allowed scope (.perform (Instantiation.freezeEffect effect) operation)
        input output [] (.request [] [⟨effect, operation, false⟩]) (.request (effect := effect) (operation := operation))
  | resume (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
      (permission : (policy binder).resume = true)
      (admitted : contract.resumeEffects ⊆ allowed) (formed : ScopedPorts.InWorld world contract.answer.erase.erase.port) :
      Context operations policy contracts world environment allowed scope (.resume binder) contract.input contract.answer
        (owner :: contract.resumeDemand) (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) (.invoke (key := ⟨owner, .resume⟩))
  | cleanup (body : Expression operations policy contracts world allowed scope environment code output demand requirements dependencies)
      (admitted : requests ⊆ allowed) :
      Context operations policy contracts world environment allowed scope (.cleanup code) (.function .unit .unit requests latent callbackDep)
        output demand (.emitAfter requirements [] (qualify true latent)) (.cleanup (needs := requests) callbackDep dependencies)
  | resource {bodyRequirements : Nat → Requirements demand} {bodyDependencies : Nat → Dependencies} {bodySignatures : ∀ identity, Signature (bodyDependencies identity)}
      (body : ∀ identity, identity ∉ world → Expression operations policy contracts (world ++ [identity])
        (.cell identity :: residual) scope environment
        (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output demand (bodyRequirements identity) (bodySignatures identity))
      (formed : ScopedPorts.InWorld world output.erase.erase.port)
      (effectsBound : residual.flatMap Instance.resources ⊆ world) (admitted : residual ⊆ allowed)
      (hidden : ∀ identity, identity ∉ world → ResourceRequirements.Hides identity (bodyRequirements identity) outward) :
      Context operations policy contracts world environment allowed scope (.resource binder code) .integer output demand outward (.resource bodySignatures)

theorem context_erase {checking : Signature dependencies}
    (source : Context operations policy contracts world environment allowed scope position input output demand requirements checking) :
    SourceDependencyFrames.Context operations.erase policy contracts.erase world environment.erase allowed scope position
      input.erase output.erase demand requirements dependencies := by
  cases source with
  | pairLeft right => exact .pairLeft (expression_erase right)
  | pairRight left => exact .pairRight (expression_erase left)
  | appFunction argument admitted => exact .appFunction (expression_erase argument) admitted
  | appArgument function admitted => exact .appArgument (expression_erase function) admitted
  | bind body => exact .bind (by simpa only [SourcePlannedTyping.environment_erase_extend] using expression_erase body)
  | branch yes no same => exact .branch (expression_erase yes) (expression_erase no) same
  | perform known admitted formed => exact .perform (operation_erase known) admitted formed
  | resume known resolved permission admitted formed => exact .resume (contract_erase_known known) resolved permission admitted formed
  | cleanup body admitted => exact .cleanup (expression_erase body) admitted
  | resource body formed effectsBound admitted hidden =>
      exact .resource (fun identity fresh => expression_erase (body identity fresh)) formed effectsBound admitted hidden

/-- The actual plain frame records the same input/output types used by the
synchronized context, including the callback or function being evaluated. -/
theorem Context.plain_frame {checking : Signature dependencies}
    (context : Context operations policy contracts world (fun _ => none) allowed plain.scope plain.context
      input output demand requirements checking)
    (scope : ScopedPorts.EffectScope contracts.erase.erase.ports plain.scope ticket)
    (inputAnnotation : input.erase.erase.port = ScopedPorts.eraseType plain.input)
    (outputAnnotation : output.erase.erase.port = ScopedPorts.eraseType plain.output) :
    SourceDependencyFrames.Frame operations.erase policy contracts.erase tables families world (.plain plain)
      input.erase output.erase demand requirements (.plain dependencies) allowed allowed :=
  .plain (context_erase context) scope inputAnnotation outputAnnotation

/-- Signature decomposition follows the existing evaluation contexts. The
right-pair case introduces a pure pending frame; the application-argument case
has already evaluated the function. The source Focus proof justifies each case. -/
inductive FocusSignature : {whole child rest : Dependencies} → Signature whole → Signature child → Signature rest → Prop where
  | pure : FocusSignature .pure .pure .pure
  | sequence : FocusSignature (.sequence child rest) child rest
  | pairRight : FocusSignature (.sequence left right) right .pure
  | appArgument : FocusSignature (.sequence function (.sequence argument body)) argument body

/-- A value performs no immediate continuation invocation. Its latent bodies
retain their independent source judgments. -/
theorem template_value_disposals
    (source : SourceTemplates.Expression operations policy contracts world allowed scope environment code result demand requirements)
    (isValue : code.IsValue) : annotateDisposals requirements = requirements := by
  induction source using SourceTemplates.Expression.rec (motive_2 := fun _ _ _ _ _ _ _ => True) with
  | stable | callable | lambda | purePair => rfl
  | pair left right ihLeft ihRight => simp only [annotateDisposals, ihLeft isValue.1, ihRight isValue.2]
  | app | bind | branch | perform | handler | resource | scopedResource | resume | discard | cleanup => cases isValue
  | _ => intros; trivial

/-- Decompose an actual evaluation focus using one synchronized derivation.
The retained context and current child agree on their intermediate value type.
Both evaluation equations use those same source witnesses. -/
theorem focus_decompose_disposals
    (source : Expression operations policy contracts world allowed scope environment whole output demand requirements checking)
    (focus : Focus whole child position) :
    ∃ (input : Value) (childDemand restDemand : List Nat) (current : Requirements childDemand) (rest : Requirements restDemand)
      (childDependencies restDependencies : Dependencies) (childSignature : Signature childDependencies) (restSignature : Signature restDependencies),
      Expression operations policy contracts world allowed scope environment child input childDemand current childSignature ∧
      Context operations policy contracts world environment allowed scope position input output restDemand rest restSignature ∧
      FocusSignature checking childSignature restSignature ∧
      demand = childDemand ++ restDemand ∧
      ∀ store receiving before,
        (evaluate store receiving before requirements =
          merge (evaluate store receiving before current) (evaluate store receiving (spendAll before childDemand) rest)) ∧
        evaluate store receiving before (annotateDisposals requirements) =
          merge (evaluate store receiving before (annotateDisposals current))
            (evaluate store receiving (spendAll before childDemand) (annotateDisposals rest)) := by
  cases source with
  | handler => cases focus
  | unit | boolean | integer | reference | «variable» => cases focus
  | lambda => cases focus
  | purePair left right => cases focus with
    | pairLeft =>
        refine ⟨_, [], [], _, _, _, _, _, _, left, .pairLeft right, .pure, rfl, ?_⟩
        intro store receiving before
        constructor <;> simp only [annotateDisposals, RecursiveRecomposition.evaluate_empty, merge, List.nil_append]
    | pairRight isValue notValue =>
        refine ⟨_, [], [], _, _, _, _, _, _, right, .pairRight (value_summary left isValue), .pure, rfl, ?_⟩
        intro store receiving before
        constructor <;> simp only [annotateDisposals, RecursiveRecomposition.evaluate_empty, merge, List.nil_append]
  | pair left right => cases focus with
    | pairLeft => exact ⟨_, _, _, _, _, _, _, _, _, left, .pairLeft right, .sequence, rfl, fun _ _ _ => ⟨RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_sequence⟩⟩
    | pairRight isValue notValue =>
        have empty := SourceTemplates.expression_value_demand (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase (expression_erase left))) isValue
        subst_vars
        refine ⟨_, _, [], _, _, _, _, _, _, right, .pairRight (value_summary left isValue), .pairRight, by simp, ?_⟩
        intro store receiving before
        constructor <;> simp only [annotateDisposals, RecursiveRequirements.evaluate_sequence, template_value_disposals (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase (expression_erase left))) isValue, RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase (expression_erase left))) isValue,
          RecursiveRecomposition.evaluate_empty, spendAll, RecursiveRecomposition.merge_empty_left, RecursiveRecomposition.merge_empty_right]
  | app function argument admitted => cases focus with
    | appFunction =>
        refine ⟨_, _, _, _, _, _, _, _, _, function, .appFunction argument admitted, .sequence, rfl, ?_⟩
        intro store receiving before
        constructor <;> simp only [annotateDisposals, RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence, PhaseRechecking.spendAll_append, merge_assoc]
    | appArgument isValue notValue =>
        have empty := SourceTemplates.expression_value_demand (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase (expression_erase function))) isValue
        subst_vars
        refine ⟨_, _, [], _, _, _, _, _, _, argument, .appArgument (value_summary function isValue) admitted, .appArgument, by simp, ?_⟩
        intro store receiving before
        constructor <;> simp only [annotateDisposals, RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence,
          template_value_disposals (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase (expression_erase function))) isValue, RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase (expression_erase function))) isValue, spendAll, List.nil_append,
          RecursiveRecomposition.merge_empty_left, evaluate_request]
  | bind initializer body => cases focus with
    | bind => exact ⟨_, _, _, _, _, _, _, _, _, initializer, .bind body, .sequence, rfl, fun _ _ _ => ⟨RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_sequence⟩⟩
  | branch condition yes no same => cases focus with
    | branch => exact ⟨_, _, _, _, _, _, _, _, _, condition, .branch yes no same, .sequence, rfl, fun _ _ _ => ⟨RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_sequence⟩⟩
  | perform known admitted operand formed => cases focus with
    | perform =>
        refine ⟨_, _, [], _, _, _, _, _, _, operand, .perform known admitted formed, .sequence, by simp, ?_⟩
        intro store receiving before
        constructor <;> simp only [annotateDisposals, RecursiveRequirements.evaluate_emit, evaluate_request, List.nil_append]
  | resource initializer body formed effectsBound admitted hidden => cases focus with
    | resource notValue =>
        exact ⟨_, _, _, _, _, _, _, _, _, initializer, .resource body formed effectsBound admitted hidden,
          .sequence, rfl, fun _ _ _ => ⟨RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_sequence⟩⟩
  | resume known resolved permission operand admitted formed => cases focus with
    | resume => exact ⟨_, _, _, _, _, _, _, _, _, operand, .resume known resolved permission admitted formed, .sequence, rfl,
        fun _ _ _ => ⟨RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_sequence⟩⟩
  | discard => cases focus
  | cleanup callback body admitted => cases focus with
    | cleanup =>
        refine ⟨_, _, _, _, _, _, _, _, _, callback, .cleanup body admitted, .sequence, rfl, ?_⟩
        intro store receiving before
        constructor <;> simp only [annotateDisposals, RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence, PhaseRechecking.spendAll_append, merge_assoc]

/-- Preserve the existing ordinary interface by projecting the paired equations. -/
theorem focus_decompose
    (source : Expression operations policy contracts world allowed scope environment whole output demand requirements checking)
    (focus : Focus whole child position) :
    ∃ (input : Value) (childDemand restDemand : List Nat) (current : Requirements childDemand) (rest : Requirements restDemand)
      (childDependencies restDependencies : Dependencies) (childSignature : Signature childDependencies) (restSignature : Signature restDependencies),
      Expression operations policy contracts world allowed scope environment child input childDemand current childSignature ∧
      Context operations policy contracts world environment allowed scope position input output restDemand rest restSignature ∧
      FocusSignature checking childSignature restSignature ∧
      demand = childDemand ++ restDemand ∧
      ∀ store receiving before, RecursiveRequirements.evaluate store receiving before requirements =
        ProtectionResiduals.merge (RecursiveRequirements.evaluate store receiving before current)
          (RecursiveRequirements.evaluate store receiving (OwnerPhaseTransitions.spendAll before childDemand) rest) := by
  obtain ⟨input, childDemand, restDemand, current, rest, childDependencies, restDependencies, childSignature, restSignature,
    childSource, context, split, same, evaluation⟩ := focus_decompose_disposals source focus
  exact ⟨input, childDemand, restDemand, current, rest, childDependencies, restDependencies, childSignature, restSignature,
    childSource, context, split, same, fun store receiving before => (evaluation store receiving before).1⟩

/-- Construct the actual focus step and its plain frame from the synchronized
source choices. Frame preparation and the owner trace reuse existing proofs.
SourcePlannedFocus adds the stronger local checks to these same choices. -/
theorem focus_step_disposals
    (source : Expression operations policy contracts world allowed scope (fun _ => none) whole output demand requirements checking)
    (focus : Focus whole child position)
    (scopeTyped : ScopedPorts.EffectScope contracts.erase.erase.ports scope ticket) :
    ∃ (input : Value) (childDemand restDemand : List Nat) (current : Requirements childDemand) (rest : Requirements restDemand)
      (childDependencies restDependencies : Dependencies) (childSignature : Signature childDependencies) (restSignature : Signature restDependencies)
      (plain : PlainData),
      RawStep ⟨whole, scope, stack⟩ ⟨child, scope, .push (.plain plain) stack⟩ [] [] ∧
      Expression operations policy contracts world allowed scope (fun _ => none) child input childDemand current childSignature ∧
      Context operations policy contracts world (fun _ => none) allowed plain.scope plain.context input output restDemand rest restSignature ∧
      SourceDependencyFrames.Frame operations.erase policy contracts.erase tables families world (.plain plain)
        input.erase output.erase restDemand rest (.plain restDependencies) allowed allowed ∧
      FocusSignature checking childSignature restSignature ∧
      demand = childDemand ++ restDemand ∧
      (∀ store receiving before,
        (evaluate store receiving before requirements =
          merge (evaluate store receiving before current) (evaluate store receiving (spendAll before childDemand) rest)) ∧
        evaluate store receiving before (annotateDisposals requirements) =
          merge (evaluate store receiving before (annotateDisposals current))
            (evaluate store receiving (spendAll before childDemand) (annotateDisposals rest))) ∧
      OwnerPhaseTransitions.Trace (OwnerPhaseTransitions.available (ownedTickets stack)) []
        (OwnerPhaseTransitions.available (ownedTickets (.push (.plain plain) stack))) := by
  obtain ⟨input, childDemand, restDemand, current, rest, childDependencies, restDependencies, childSignature, restSignature,
    childSource, context, split, same, evaluation⟩ := focus_decompose_disposals source focus
  obtain ⟨plain, contextSame, scopeSame, inputAnnotation, outputAnnotation⟩ := RecursiveContexts.prepare_plain
    (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase (expression_erase source)))
    focus scopeTyped input.erase.erase
  have synchronized : Context operations policy contracts world (fun _ => none) allowed plain.scope plain.context
      input output restDemand rest restSignature := by simpa only [contextSame, scopeSame] using context
  refine ⟨input, childDemand, restDemand, current, rest, childDependencies, restDependencies, childSignature, restSignature,
    plain, ?_, childSource, synchronized,
    synchronized.plain_frame (by simpa only [scopeSame] using scopeTyped) inputAnnotation outputAnnotation, split, same, evaluation, .nil⟩
  simpa only [scopeSame] using RawStep.focus plain (by simpa only [contextSame] using focus) stack

/-- Preserve the existing ordinary interface by projecting the paired equations. -/
theorem focus_step
    (source : Expression operations policy contracts world allowed scope (fun _ => none) whole output demand requirements checking)
    (focus : Focus whole child position)
    (scopeTyped : ScopedPorts.EffectScope contracts.erase.erase.ports scope ticket) :
    ∃ (input : Value) (childDemand restDemand : List Nat) (current : Requirements childDemand) (rest : Requirements restDemand)
      (childDependencies restDependencies : Dependencies) (childSignature : Signature childDependencies) (restSignature : Signature restDependencies)
      (plain : PlainData),
      RawStep ⟨whole, scope, stack⟩ ⟨child, scope, .push (.plain plain) stack⟩ [] [] ∧
      Expression operations policy contracts world allowed scope (fun _ => none) child input childDemand current childSignature ∧
      Context operations policy contracts world (fun _ => none) allowed plain.scope plain.context input output restDemand rest restSignature ∧
      SourceDependencyFrames.Frame operations.erase policy contracts.erase tables families world (.plain plain)
        input.erase output.erase restDemand rest (.plain restDependencies) allowed allowed ∧
      demand = childDemand ++ restDemand ∧
      (∀ store receiving before, evaluate store receiving before requirements =
        merge (evaluate store receiving before current) (evaluate store receiving (spendAll before childDemand) rest)) ∧
      OwnerPhaseTransitions.Trace (OwnerPhaseTransitions.available (ownedTickets stack)) []
        (OwnerPhaseTransitions.available (ownedTickets (.push (.plain plain) stack))) := by
  obtain ⟨input, childDemand, restDemand, current, rest, childDependencies, restDependencies,
    childSignature, restSignature, plain, step, childSource, context, frame, split, same, evaluation, trace⟩ :=
    focus_step_disposals source focus scopeTyped
  exact ⟨input, childDemand, restDemand, current, rest, childDependencies, restDependencies,
    childSignature, restSignature, plain, step, childSource, context, frame, same,
    fun store receiving before => (evaluation store receiving before).1, trace⟩


end Ash.OneShot.SourcePlannedSources

#print axioms Ash.OneShot.SourcePlannedSources.value_change_scope
#print axioms Ash.OneShot.SourcePlannedSources.value_summary
#print axioms Ash.OneShot.SourcePlannedSources.context_erase
#print axioms Ash.OneShot.SourcePlannedSources.Context.plain_frame

#print axioms Ash.OneShot.SourcePlannedSources.focus_decompose

#print axioms Ash.OneShot.SourcePlannedSources.value_pure

#print axioms Ash.OneShot.SourcePlannedSources.focus_step

#print axioms Ash.OneShot.SourcePlannedSources.template_value_disposals

#print axioms Ash.OneShot.SourcePlannedSources.focus_decompose_disposals

#print axioms Ash.OneShot.SourcePlannedSources.focus_step_disposals
