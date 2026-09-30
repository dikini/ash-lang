import SourceDependencyScopes

namespace Ash.OneShot.SourceDependencyCapture
/-- The source-scope change of a permitted administrative unwind step. Runtime
Advance separately determines whether the leading frame may be removed. -/
def Scope.afterUnwind : Scope → Scope
  | .plain _ rest | .handler _ _ _ rest | .cell _ rest | .running rest | .spent _ rest => rest
  | .live _ saved rest => saved.append (.running rest)
  | scope => scope
end Ash.OneShot.SourceDependencyCapture

/-! Retained source code authenticates dependency scopes at the same enriched
value, owner-demand and requirement indices. The old shared source/effect
segment is recovered by erasure. This does not assert that every retained
computation passes the local capture guard. -/
namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Value Environment Operations Contract Contracts Expression Body Offer Declarations Dependencies ValueSummary)
open RecursiveRequirements (Requirements Store)
abbrev DependencyScope := SourceDependencyCapture.Scope
abbrev Families := SourceDependencyCapture.Families

theorem value_erase (source : ValueSummary operations policy contracts world environment allowed code value) :
    DeclaredSourceValues.ValueSummary operations.erase policy contracts.erase world environment.erase allowed code value.erase :=
  DeclaredSourceValues.request_callable (SourceDependencyAnnotations.expression_erase source) [] rfl

/-- Canonical forms transfer the lambda's finite effect bound to every actual
closed function value, including values returned through prior computation. -/
theorem function_latent_bound
    (source : ValueSummary operations policy contracts world environment allowed code
      (.function input output requests latent dependencies))
    (closed : ClosedValue code) :
    ∀ request ∈ latent, request.effect ∈ requests := by
  have ports := (DeclaredSourceValues.erase (value_erase source)).ports .none
  obtain ⟨parameter, body, same⟩ := ScopedPorts.typed_function_value ports closed.1
  rw [same] at source
  exact SourceDependencyAnnotations.lambda_latent_bound source

theorem function_empty_latent
    (source : ValueSummary operations policy contracts world environment allowed code
      (.function input output [] latent dependencies))
    (closed : ClosedValue code) : latent = [] := by
  cases latent with
  | nil => rfl
  | cons request rest => exact False.elim (List.not_mem_nil (function_latent_bound source closed request List.mem_cons_self))

theorem body_erase (source : Body operations policy contracts world allowed scope environment code value header dependencies) :
    DeclaredSources.Body operations.erase policy contracts.erase world allowed scope environment.erase code value.erase header := by
  cases source with
  | typed body rows => exact .typed (SourceDependencyAnnotations.expression_erase body) rows
  | annotated body annotation rows => exact .typed (SourceDependencyAnnotations.expression_erase body) (annotation.rows rows)

theorem offer_erase
    (source : Offer operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held disposes row dependencies) :
    DeclaredSources.Offer operations.erase policy contracts.erase world environment.erase allowed parameter binder
      argument.erase input.erase answer.erase resumeEffects closeEffects code held disposes row := by
  cases source with
  | unavailable => exact .unavailable
  | available resumeInterface closeInterface source =>
      apply DeclaredSources.Offer.available resumeInterface closeInterface
      intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
      have result := body_erase (source owner (SourceDependencyAnnotations.Contract.refine contract _ _)
        (Option.map_eq_none_iff.mp fresh) rfl rfl resumeSame closeSame heldSame balance)
      simpa only [SourceDependencyAnnotations.contracts_erase_insert, SourceDependencyAnnotations.environment_erase_extend,
        SourceDependencyAnnotations.contract_refine_erase inputSame answerSame] using result

theorem declarations_erase
    (source : Declarations operations policy contracts world environment allowed effect answer clauses table dependencies) :
    DeclaredSources.Declarations operations.erase policy contracts.erase world environment.erase allowed effect answer.erase clauses table := by
  induction clauses using Clauses.rec (motive_1 := fun _ => True) generalizing table dependencies
  case nil => cases source; exact .nil
  case cons operation parameter binder body rest ihBody ihRest => cases source with
    | cons known ordinary protectedMode rest =>
        exact .cons (SourceDependencyAnnotations.operation_erase known) (offer_erase ordinary) (offer_erase protectedMode) (ihRest rest)
  all_goals trivial

inductive Context (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (world : List Nat) (environment : Environment) (allowed : List Instance) (scope : Execution.Scope) :
    ScopedExecution.Context → Value → Value → (demand : List Nat) → Requirements demand → Dependencies → Prop where
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
      (formed : ScopedPorts.InWorld world output.erase.port) :
      Context operations policy contracts world environment allowed scope (.perform (Instantiation.freezeEffect effect) operation)
        input output [] (.request [] [⟨effect, operation, false⟩]) (.request effect operation)
  | resume (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
      (permission : (policy binder).resume = true)
      (admitted : contract.resumeEffects ⊆ allowed) (formed : ScopedPorts.InWorld world contract.answer.erase.port) :
      Context operations policy contracts world environment allowed scope (.resume binder) contract.input contract.answer
        (owner :: contract.resumeDemand) (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) (.invoke ⟨owner, .resume⟩)
  | cleanup (body : Expression operations policy contracts world allowed scope environment code output demand requirements dependencies)
      (admitted : requests ⊆ allowed) :
      Context operations policy contracts world environment allowed scope (.cleanup code) (.function .unit .unit requests latent callbackDep)
        output demand (.emitAfter requirements [] (qualify true latent)) (.cleanup requests callbackDep dependencies)
  | resource {bodyRequirements : Nat → Requirements demand} {bodyDependencies : Nat → Dependencies}
      (body : ∀ identity, identity ∉ world → Expression operations policy contracts (world ++ [identity])
        (.cell identity :: residual) scope environment
        (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output demand (bodyRequirements identity) (bodyDependencies identity))
      (formed : ScopedPorts.InWorld world output.erase.port)
      (effectsBound : residual.flatMap Instance.resources ⊆ world) (admitted : residual ⊆ allowed)
      (hidden : ∀ identity, identity ∉ world → ResourceRequirements.Hides identity (bodyRequirements identity) outward) :
      Context operations policy contracts world environment allowed scope (.resource binder code) .integer output demand outward (.resource bodyDependencies)

theorem context_erase
    (source : Context operations policy contracts world environment allowed scope position input output demand requirements dependencies) :
    DeclaredSourceFrames.Context operations.erase policy contracts.erase world environment.erase allowed scope position input.erase output.erase demand requirements := by
  cases source with
  | pairLeft right => exact .pairLeft (SourceDependencyAnnotations.expression_erase right)
  | pairRight left => exact .pairRight (value_erase left)
  | appFunction argument admitted => exact .appFunction (SourceDependencyAnnotations.expression_erase argument) admitted
  | appArgument function admitted => exact .appArgument (value_erase function) admitted
  | bind body => exact .bind (by simpa only [SourceDependencyAnnotations.environment_erase_extend] using SourceDependencyAnnotations.expression_erase body)
  | branch yes no same => exact .branch (SourceDependencyAnnotations.expression_erase yes) (SourceDependencyAnnotations.expression_erase no) same
  | perform known admitted formed => exact .perform (SourceDependencyAnnotations.operation_erase known) admitted formed
  | resume known resolved permission admitted formed => exact .resume (SourceDependencyAnnotations.contract_erase_known known) resolved permission admitted formed
  | cleanup body admitted => exact .cleanup (SourceDependencyAnnotations.expression_erase body) admitted
  | resource body formed effectsBound admitted hidden =>
      exact .scopedResource (fun identity fresh => SourceDependencyAnnotations.expression_erase (body identity fresh)) formed effectsBound admitted hidden

inductive Frame (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (families : Families) (world : List Nat) :
    ExecFrame → Value → Value → (demand : List Nat) → Requirements demand → (DependencyScope → DependencyScope) →
      List Instance → List Instance → Prop where
  | plain
      (context : Context operations policy contracts world Environment.empty allowed plain.scope plain.context input output demand requirements dependencies)
      (scope : ScopedPorts.EffectScope contracts.erase.ports plain.scope ticket)
      (inputAnnotation : input.erase.port = ScopedPorts.eraseType plain.input)
      (outputAnnotation : output.erase.port = ScopedPorts.eraseType plain.output) :
      Frame operations policy contracts tables families world (.plain plain) input output demand requirements (.plain dependencies) allowed allowed
  | handler
      (scope : ScopedPorts.EffectScopeKnown contracts.erase.ports handler.scope)
      (annotation : answer.erase.port = ScopedPorts.eraseType handler.answer)
      (clauses : ScopedPorts.ClausesTyped operations.erase.ports world Environment.empty.erase.ports handler.effectInst answer.erase.port residual handler.clauses)
      (coverage : ScopedPorts.Covers operations.erase.ports handler.effectInst handler.clauses)
      (unique : (ScopedTyping.clauseKeys handler.clauses).Nodup)
      (declarations : Declarations operations policy contracts world Environment.empty residual handler.effectInst answer handler.clauses (tables handler) (families handler))
      (capabilities : ClausesUse policy handler.clauses)
      (modes : SourceTemplates.ClauseModes handler.clauses (tables handler)) :
      Frame operations policy contracts tables families world (.handler handler) answer answer [] (.request [] [])
        (.handler handler.effectInst (tables handler) (families handler)) (handler.effectInst :: residual) residual
  | cell (scopeKnown : ScopedPorts.ScopeKnown contracts.erase.ports.types caller)
      (noEscape : identity ∉ (ScopedPorts.eraseType answer).resources)
      (annotation : result.erase.port = ScopedPorts.eraseType answer)
      (interface : ScopedPorts.EffectFrame operations.erase.ports contracts.erase.ports world (.cell identity payload caller answer) incoming outgoing) :
      Frame operations policy contracts tables families world (.cell identity payload caller answer) result result [] (.request [] []) (.cell identity) incoming outgoing
  | armed (scopeKnown : ScopedPorts.ScopeKnown contracts.erase.ports.types action.scope)
      (callback : ValueSummary operations policy contracts world Environment.empty [] action.action (.function .unit .unit action.requests latent callbackDep))
      (annotation : result.erase.port = ScopedPorts.eraseType action.answer)
      (interface : ScopedPorts.EffectFrame operations.erase.ports contracts.erase.ports world (.armed action) incoming outgoing) :
      Frame operations policy contracts tables families world (.armed action) result result [] (.request [] (qualify true latent))
        (.cleanup action.requests callbackDep) incoming outgoing
  | running (scopeKnown : ScopedPorts.ScopeKnown contracts.erase.ports.types action.scope)
      (callback : ValueSummary operations policy contracts world Environment.empty [] action.action (.function .unit .unit action.requests latent callbackDep))
      (saved : ValueSummary operations policy contracts world Environment.empty [] value result)
      (annotation : result.erase.port = ScopedPorts.eraseType action.answer)
      (interface : ScopedPorts.EffectFrame operations.erase.ports contracts.erase.ports world (.running action value closed) incoming outgoing) :
      Frame operations policy contracts tables families world (.running action value closed) .unit result [] (.request [] []) .running incoming outgoing
  | closing (scopeKnown : ScopedPorts.ScopeKnown contracts.erase.ports.types caller)
      (interface : ScopedPorts.EffectFrame operations.erase.ports contracts.erase.ports world (.closing identity caller) incoming outgoing) :
      Frame operations policy contracts tables families world (.closing identity caller) .unit .unit [] (.request [] []) .running incoming outgoing
  | retiring (known : contracts owner = some contract)
      (interface : ScopedPorts.EffectFrame operations.erase.ports contracts.erase.ports world (.retiring owner) incoming outgoing) :
      Frame operations policy contracts tables families world (.retiring owner) .unit .unit [owner] (.retire owner) .running incoming outgoing

theorem Frame.erase
    (frame : Frame operations policy contracts tables families world entry input output demand requirements layer incoming outgoing) :
    DeclaredConnectedSources.Frame operations.erase policy contracts.erase tables world entry input.erase output.erase demand requirements incoming outgoing := by
  cases frame with
  | plain context scope inputAnnotation outputAnnotation => exact .plain (context_erase context) scope inputAnnotation outputAnnotation
  | handler scope annotation clauses coverage unique declarations capabilities modes =>
      exact .handler scope annotation clauses coverage unique (declarations_erase declarations) capabilities modes
  | cell scopeKnown noEscape annotation interface => exact .retained .cell (.cell scopeKnown noEscape annotation) interface
  | armed scopeKnown callback annotation interface => exact .retained .armed (.armed scopeKnown (value_erase callback) annotation) interface
  | running scopeKnown callback saved annotation interface => exact .retained .running (.running scopeKnown (value_erase callback) (value_erase saved) annotation) interface
  | closing scopeKnown interface => exact .retained .closing (.closing scopeKnown) interface
  | retiring known interface => exact .retained .retiring (.retiring (SourceDependencyAnnotations.contract_erase_known known)) interface

theorem Frame.realizes
    (frame : Frame operations policy contracts tables families world entry input output demand requirements layer incoming outgoing) :
    SourceDependencyCapture.Frame tables families layer entry := by
  cases frame with
  | plain => exact .plain
  | handler => exact .handler
  | cell => exact .cell
  | armed => exact .cleanup
  | running => exact .running
  | closing => exact .closing
  | retiring => exact .retiring


/-- Increasing only the exported interface keeps every internal handler
boundary and historical source derivation unchanged. -/
theorem erased_outgoing_weaken
    (segment : DeclaredConnectedSources.Segment operations policy contracts tables actions world
      stack input output demand requirements records incoming outgoing)
    (grow : outgoing ⊆ larger) :
    DeclaredConnectedSources.Segment operations policy contracts tables actions world
      stack input output demand requirements records incoming larger := by
  induction segment with
  | nil bound => exact .nil (List.Subset.trans bound grow)
  | push head tail bound ih => exact .push head (ih grow) bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedInterface tail resume close bound ihSaved ihTail =>
      exact .live known actionKnown inputAnnotation answerAnnotation scope held saved savedInterface (ihTail grow) resume close bound
  | spent known annotation scope tail bound ih => exact .spent known annotation scope (ih grow) bound

/-- Adjacent frames agree on enriched values, including latent dependencies.
Dormant captures keep their source derivation even when resumption is denied;
only an offered resumption requires its executable interface. -/
inductive Segment (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (families : Families) (actions : Syntax.UsageTickets) (world : List Nat) :
    Stack → Value → Value → (demand : List Nat) → Requirements demand → Store → DependencyScope →
      List Instance → List Instance → Prop where
  | nil (bound : incoming ⊆ outgoing) :
      Segment operations policy contracts tables families actions world .nil result result [] (.request [] []) [] .nil incoming outgoing
  | push (head : Frame operations policy contracts tables families world entry input middle headDemand first layer inner outer)
      (tail : Segment operations policy contracts tables families actions world rest middle output tailDemand second records restScope outer outgoing)
      (bound : incoming ⊆ inner) :
      Segment operations policy contracts tables families actions world (.push entry rest) input output
        (headDemand ++ tailDemand) (.sequence (first.prepend (OwnerPhases.ofStack tables rest)) second) records (layer restScope) incoming outgoing
  | live (known : contracts owner = some contract) (actionKnown : actions owner = some rights)
      (inputAnnotation : contract.input.erase.port = ScopedPorts.eraseType inputType)
      (answerAnnotation : contract.answer.erase.port = ScopedPorts.eraseType answerType)
      (scope : ScopedPorts.EffectScopeKnown contracts.erase.ports caller)
      (held : contract.held = ProtectionContexts.protectedMode capture.erase)
      (saved : Segment operations policy contracts tables families actions world
        capture contract.input contract.answer contract.resumeDemand body nested savedScope [] savedBoundary)
      (savedBound : rights.resume = true → savedBoundary ⊆ contract.resumeEffects)
      (tail : Segment operations policy contracts tables families actions world rest contract.answer output
        demand requirements remaining restScope boundary outgoing)
      (resume : rights.resume = true → contract.resumeEffects ⊆ boundary)
      (close : rights.dispose = true → contract.closeEffects ⊆ boundary)
      (bound : incoming ⊆ boundary) :
      Segment operations policy contracts tables families actions world (.live owner inputType answerType capture caller rest)
        contract.answer output demand (.sequence (.spent owner) requirements)
        ((⟨owner, .resume⟩, ⟨contract.resumeDemand, body⟩) :: (nested ++ remaining)) (.live owner savedScope restScope) incoming outgoing
  | spent (known : contracts owner = some contract)
      (annotation : contract.answer.erase.port = ScopedPorts.eraseType answerType)
      (scope : ScopedPorts.EffectScopeKnown contracts.erase.ports caller)
      (tail : Segment operations policy contracts tables families actions world rest contract.answer output
        demand requirements records restScope boundary outgoing)
      (bound : incoming ⊆ boundary) :
      Segment operations policy contracts tables families actions world (.spent owner answerType caller rest) contract.answer output
        demand (.sequence (.spent owner) requirements) records (.spent owner restScope) incoming outgoing

theorem Segment.erase
    (segment : Segment operations policy contracts tables families actions world stack input output demand requirements records dependencyScope incoming outgoing) :
    DeclaredConnectedSources.Segment operations.erase policy contracts.erase tables actions world stack input.erase output.erase demand requirements records incoming outgoing := by
  induction segment with
  | nil bound => exact .nil bound
  | push head tail bound ih => exact .push head.erase ih bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live (SourceDependencyAnnotations.contract_erase_known known) actionKnown inputAnnotation answerAnnotation scope held
        ihSaved.source (fun used => erased_outgoing_weaken ihSaved (savedBound used)) ihTail resume close bound
  | spent known annotation scope tail bound ih =>
      exact .spent (SourceDependencyAnnotations.contract_erase_known known) annotation scope ih bound

theorem Segment.realizes
    (segment : Segment operations policy contracts tables families actions world stack input output demand requirements records dependencyScope incoming outgoing) :
    SourceDependencyCapture.Realizes tables families dependencyScope stack := by
  induction segment with
  | nil => exact .nil
  | push head tail bound ih => exact .push head.realizes ih
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live ihSaved ihTail
  | spent known annotation scope tail bound ih => exact .spent ih


open ProtectionResiduals
open RecursiveRequirements (evaluate)
open OwnerPhaseTransitions (spendAll)

/-- Restricting entry requirements does not alter any retained annotation. -/
theorem Segment.input_weaken
    (segment : Segment operations policy contracts tables families actions world stack input output demand requirements records dependencyScope incoming outgoing)
    (shrink : smaller ⊆ incoming) :
    Segment operations policy contracts tables families actions world stack input output demand requirements records dependencyScope smaller outgoing := by
  cases segment with
  | nil bound => exact .nil (List.Subset.trans shrink bound)
  | push head tail bound => exact .push head tail (List.Subset.trans shrink bound)
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound =>
      exact .live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close (List.Subset.trans shrink bound)
  | spent known annotation scope tail bound => exact .spent known annotation scope tail (List.Subset.trans shrink bound)

/-- The actual handler cut retains enriched values, source dependencies and
all owner records. The evaluation calculation reuses the old capture proof's
recursive equations; no independent choice of annotations is made. -/
theorem capture_segments
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy contracts tables families actions world whole input output demand requirements records wholeScope incoming outgoing) :
    ∃ (answer : Value) (residual : List Instance) (capturedDemand tailDemand : List Nat)
      (capturedRequirements : Requirements capturedDemand) (tailRequirements : Requirements tailDemand)
      (capturedRecords tailRecords : Store) (capturedScope tailScope : DependencyScope),
      answer.erase.port = ScopedPorts.eraseType handler.answer ∧ Frame operations policy contracts tables families world (.handler handler) answer answer [] (.request [] [])
        (.handler handler.effectInst (tables handler) (families handler)) (handler.effectInst :: residual) residual ∧
      Segment operations policy contracts tables families actions world capture input answer capturedDemand capturedRequirements capturedRecords capturedScope incoming residual ∧
      Segment operations policy contracts tables families actions world tail answer output tailDemand tailRequirements tailRecords tailScope residual outgoing ∧
      wholeScope = capturedScope.append tailScope ∧
      demand = capturedDemand ++ tailDemand ∧ records = capturedRecords ++ tailRecords ∧
      (∀ operation, SourceDependencyCapture.select requested operation wholeScope =
        SourceDependencyCapture.chosen operation (tables handler) (families handler) capturedScope tailScope) ∧
      ∀ store receiving before, evaluate store receiving before requirements =
        merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) before capturedRequirements)
          (evaluate store receiving (spendAll before capturedDemand) tailRequirements) := by
  induction cut generalizing input demand requirements records wholeScope incoming with
  | hit handler tail same => cases source with
    | push current rest bound => cases current with
      | handler scope annotation clauses coverage unique declarations capabilities modes =>
          have frame := Frame.handler scope annotation clauses coverage unique declarations capabilities modes
          refine ⟨_, _, [], _, _, _, [], _, _, _, annotation, frame,
            .push frame (.nil (List.Subset.refl _)) bound, rest, rfl, rfl, rfl, ?_, ?_⟩
          · intro operation
            simp only [SourceDependencyCapture.select, if_pos same.symm, SourceDependencyCapture.chosen]
            rfl
          intro store receiving before
          simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
            RecursiveRecomposition.evaluate_empty, spendAll, RecursiveRecomposition.merge_empty_left]
  | push entry rest cap tail handler miss next ih => cases source with
    | push current rest bound =>
        obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
          annotation, selected, saved, outside, sameScope, sameDemand, sameRecords, selection, evaluation⟩ := ih rest
        refine ⟨answer, residual, _, tailDemand, _, tailReq, capRecords, tailRecords, _, tailScope, annotation, selected, .push current saved bound, outside,
          by rw [current.realizes.append, ← sameScope],
          by simp only [sameDemand, List.append_assoc], sameRecords, ?_, ?_⟩
        · intro operation
          rw [current.realizes.select_miss miss, selection operation, SourceDependencyCapture.chosen_prepend]
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, evaluation,
          handler_cut_reconstructs next, OwnerPhases.stack_append, List.append_assoc,
          PhaseRechecking.spendAll_append, merge_assoc]
  | live owner inputType answerType savedScope caller rest cap tail handler next ih => cases source with
    | live known actionKnown inputAnnotation answerAnnotation scopeKnown held historical savedInterface rest resume close bound =>
        obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
          annotation, selected, saved, outside, sameScope, sameDemand, sameRecords, selection, evaluation⟩ := ih rest
        refine ⟨answer, residual, capDemand, tailDemand, _, tailReq, _, tailRecords, _, tailScope, annotation, selected,
          .live known actionKnown inputAnnotation answerAnnotation scopeKnown held historical savedInterface saved resume close bound, outside,
          by simp only [SourceDependencyCapture.Scope.append, ← sameScope], sameDemand, ?_, ?_, ?_⟩
        · simp only [sameRecords, List.cons_append, List.append_assoc]
        · intro operation
          rw [SourceDependencyCapture.select, selection operation, SourceDependencyCapture.chosen_prepend]
        · intro store receiving before
          simp only [RecursiveRequirements.evaluate_sequence, evaluation, RecursiveRecomposition.evaluate_spent,
            spendAll, merge_assoc]
  | spent owner answerType caller rest cap tail handler next ih => cases source with
    | spent known answerAnnotation scopeKnown rest bound =>
        obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
          annotation, selected, saved, outside, sameScope, sameDemand, sameRecords, selection, evaluation⟩ := ih rest
        refine ⟨answer, residual, capDemand, tailDemand, _, tailReq, capRecords, tailRecords, _, tailScope, annotation, selected,
          .spent known answerAnnotation scopeKnown saved bound, outside, by simp only [SourceDependencyCapture.Scope.append, ← sameScope], sameDemand, sameRecords, ?_, ?_⟩
        · intro operation
          rw [SourceDependencyCapture.select, selection operation, SourceDependencyCapture.chosen_prepend]
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_sequence, evaluation, RecursiveRecomposition.evaluate_spent,
          spendAll, merge_assoc]


open RecursiveRecomposition (evaluate_empty evaluate_spent merge_empty_left)
variable {front tail : Stack}

/-- Recomposition preserves the exact source scope and enriched intermediate
value. Existing append, phase and evaluation laws discharge the accounting. -/
theorem segment_append
    (first : Segment operations policy contracts tables families actions world front input middle
      firstDemand firstRequirements firstRecords firstScope incoming boundary)
    (second : Segment operations policy contracts tables families actions world tail middle output
      secondDemand secondRequirements secondRecords secondScope boundary outgoing) :
    ∃ combined : Requirements (firstDemand ++ secondDemand),
      Segment operations policy contracts tables families actions world (front.append tail) input output
        (firstDemand ++ secondDemand) combined (firstRecords ++ secondRecords) (firstScope.append secondScope) incoming outgoing ∧
      ∀ store receiving phases,
        evaluate store receiving phases combined =
          merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) phases firstRequirements)
            (evaluate store receiving (spendAll phases firstDemand) secondRequirements) := by
  induction first generalizing output secondDemand secondRequirements secondRecords secondScope tail outgoing with
  | nil bound =>
      refine ⟨secondRequirements, second.input_weaken bound, ?_⟩
      intro store receiving phases
      simp only [evaluate_empty, spendAll, merge_empty_left]
  | push head rest bound ih =>
      obtain ⟨combined, source, evaluation⟩ := ih second
      rw [List.append_assoc]
      have rebuilt := Segment.push head source bound
      rw [← head.realizes.append] at rebuilt
      refine ⟨_, rebuilt, ?_⟩
      intro store receiving phases
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        OwnerPhases.stack_append, List.append_assoc, evaluation, PhaseRechecking.spendAll_append, merge_assoc]
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedInterface rest resume close bound ihSaved ihRest =>
      obtain ⟨combined, source, evaluation⟩ := ihRest second
      have rebuilt := Segment.live known actionKnown inputAnnotation answerAnnotation scope held saved savedInterface source resume close bound
      simp only [List.cons_append, List.append_assoc]
      refine ⟨_, rebuilt, ?_⟩
      intro store receiving phases
      simp only [RecursiveRequirements.evaluate_sequence, evaluate_spent, evaluation, spendAll, merge_assoc]
  | spent known annotation scope rest bound ih =>
      obtain ⟨combined, source, evaluation⟩ := ih second
      refine ⟨_, .spent known annotation scope source bound, ?_⟩
      intro store receiving phases
      simp only [RecursiveRequirements.evaluate_sequence, evaluate_spent, evaluation, spendAll, merge_assoc]


/-- Source typing supplies ordinary callback typing and the exact scope at the
actual cut. The local guard supplies closing compatibility. The existing plan
constructor supplies its owner accounting; no independent scope or plan witness
is assumed. Establishing this guard from initial source remains separate. -/
theorem capture_plan
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy contracts tables families actions world whole input output demand requirements records wholeScope incoming outgoing)
    (checked : SourceDependencyCapture.checkCapture outward wholeScope requested operation = true)
    (known : lookup operation (tables handler) = some offered)
    (disposes : offered.dispose = true)
    (supported : Supported capture.erase (Admission.outsideResources capture.erase)) :
    ∃ (answer : Value) (residual : List Instance) (capturedDemand tailDemand : List Nat)
      (capturedRequirements : Requirements capturedDemand) (tailRequirements : Requirements tailDemand)
      (capturedRecords tailRecords : Store) (capturedScope tailScope : DependencyScope)
      (plan : List CloseEntry),
      makePlan capture = some plan ∧
      ScopedPorts.PlanTyped operations.erase.ports world outward plan ∧
      Admission.OpenCloses capture.erase .nil .nil (Admission.outsideResources capture.erase)
        outward (plan.map CloseEntry.erase) ∧
      Segment operations policy contracts tables families actions world capture input answer capturedDemand capturedRequirements capturedRecords capturedScope incoming residual ∧
      Segment operations policy contracts tables families actions world tail answer output tailDemand tailRequirements tailRecords tailScope residual outgoing ∧
      wholeScope = capturedScope.append tailScope ∧ demand = capturedDemand ++ tailDemand ∧ records = capturedRecords ++ tailRecords ∧
      (planOwners (plan.map CloseEntry.erase)).Perm capture.erase.owners := by
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
    annotation, selected, saved, outside, sameScope, sameDemand, sameRecords, selection, evaluation⟩ := capture_segments cut source
  cases annotated : SourceDependencyCapture.lookupDependencies operation (families handler) with
  | none =>
      have absent : SourceDependencyCapture.select requested operation wholeScope = none := by
        simpa only [SourceDependencyCapture.chosen, known, annotated] using selection operation
      simp [SourceDependencyCapture.checkCapture, absent] at checked
  | some modes =>
      have found : SourceDependencyCapture.select requested operation wholeScope = some (.handler capScope tailScope offered modes) := by
        simpa only [SourceDependencyCapture.chosen, known, annotated] using selection operation
      obtain ⟨unprotected, closing, available⟩ := SourceDependencyCapture.disposing_capture checked found disposes
      obtain ⟨plan, shape⟩ := saved.realizes.closing unprotected
      obtain ⟨typed, closes⟩ := shape.interfaces closing SourceRecursiveRoutes.Scope.nil SourceRecursiveRoutes.Scope.nil
        supported (List.nil_subset _) (SourceTemplates.segment_ports saved.erase.source.erase)
      exact ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
        plan, shape.built, typed, closes, saved, outside, sameScope, sameDemand, sameRecords, shape.owner_accounting⟩

/-- Add the independent owner-use condition to the already constructed plan.
The existing certificate API keeps its source and ownership results. -/
theorem capture_certificate
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy contracts tables families actions world whole input output demand requirements records wholeScope incoming outgoing)
    (checked : SourceDependencyCapture.checkCapture record.annotation.closeEffects wholeScope requested operation = true)
    (known : lookup operation (tables handler) = some offered)
    (disposes : offered.dispose = true)
    (supported : Supported capture.erase (Admission.outsideResources capture.erase))
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending) :
    ∃ (answer : Value) (residual : List Instance) (capturedDemand tailDemand : List Nat)
      (capturedRequirements : Requirements capturedDemand) (tailRequirements : Requirements tailDemand)
      (capturedRecords tailRecords : Store) (capturedScope tailScope : DependencyScope)
      (certificate : DeclaredClosingInvariant.Certificate operations.erase.ports world record capture),
      Segment operations policy contracts tables families actions world capture input answer capturedDemand capturedRequirements capturedRecords capturedScope incoming residual ∧
      Segment operations policy contracts tables families actions world tail answer output tailDemand tailRequirements tailRecords tailScope residual outgoing ∧
      wholeScope = capturedScope.append tailScope ∧ demand = capturedDemand ++ tailDemand ∧ records = capturedRecords ++ tailRecords ∧
      (planOwners (certificate.plan.map CloseEntry.erase)).Perm capture.erase.owners := by
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
    plan, built, typed, closes, saved, outside, sameScope, sameDemand, sameRecords, owners⟩ :=
    capture_plan cut source checked known disposes supported
  exact ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
    ⟨plan, built, typed, closes, internal⟩, saved, outside, sameScope, sameDemand, sameRecords, owners⟩


theorem Segment.outgoing_weaken
    (segment : Segment operations policy contracts tables families actions world stack input output demand requirements records dependencyScope incoming outgoing)
    (grow : outgoing ⊆ larger) :
    Segment operations policy contracts tables families actions world stack input output demand requirements records dependencyScope incoming larger := by
  induction segment with
  | nil bound => exact .nil (List.Subset.trans bound grow)
  | push head tail bound ih => exact .push head (ih grow) bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound (ihTail grow) resume close bound
  | spent known annotation scope tail bound ih => exact .spent known annotation scope (ih grow) bound

open RecursiveRecomposition (normalize_replaced move_records)
variable {capture : Stack}

/-- Extract the saved source independently of whether resumption is offered,
and replace only
the consumed live boundary. Existing record and phase transport proves the
one-shot accounting through every caller prefix, including other captures. -/
theorem extract_live
    (source : Segment operations policy contracts tables families actions world
      (front.append (.live owner inputType answerType capture caller tail)) input output demand requirements records wholeScope incoming outgoing)
    (known : contracts owner = some contract) (actionKnown : actions owner = some rights) :
    ∃ (capturedRequirements : Requirements contract.resumeDemand) (capturedRecords : Store)
      (waitingRequirements : Requirements demand) (waitingRecords : Store) (capturedScope waitingScope : DependencyScope) (capturedBoundary : List Instance),
      Segment operations policy contracts tables families actions world capture contract.input contract.answer
        contract.resumeDemand capturedRequirements capturedRecords capturedScope [] capturedBoundary ∧
      (rights.resume = true → capturedBoundary ⊆ contract.resumeEffects) ∧
      Segment operations policy contracts tables families actions world (front.append (.spent owner answerType caller tail)) input output
        demand waitingRequirements waitingRecords waitingScope incoming outgoing ∧
      records.Perm ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (capturedRecords ++ waitingRecords)) ∧
      (∃ frontScope tailScope, SourceDependencyCapture.Realizes tables families frontScope front ∧
        wholeScope = frontScope.append (.live owner capturedScope tailScope) ∧
        waitingScope = frontScope.append (.spent owner tailScope)) ∧
      ∀ store receiving phases, phases owner = .consumed →
        evaluate store receiving phases waitingRequirements = evaluate store receiving phases requirements := by
  induction front generalizing input demand requirements records wholeScope incoming with
  | nil => cases source with
      | live actual actualAction inputAnnotation answerAnnotation scope held saved savedInterface rest resume close bound =>
          have same := Option.some.inj (actual.symm.trans known)
          have sameRights := Option.some.inj (actualAction.symm.trans actionKnown)
          cases same
          cases sameRights
          refine ⟨_, _, _, _, _, _, _, saved, savedInterface, .spent known answerAnnotation scope rest bound, .refl _, ⟨.nil, _, .nil, rfl, rfl⟩, ?_⟩
          intros; rfl
  | push frame front ih => cases source with
      | @push entry input middle headDemand headReq layer inner outer restStack output tailDemand tailReq records restScope outgoing incoming head rest bound =>
          obtain ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, capturedScope, waitingScope, capturedBoundary, saved, savedInterface, waiting, permutation, scopeSplit, evaluation⟩ := ih rest
          obtain ⟨frontScope, tailScope, frontRealized, wholeSame, waitingSame⟩ := scopeSplit
          refine ⟨capturedReq, capturedRecords, _, waitingRecords, capturedScope, _, capturedBoundary, saved, savedInterface, .push head waiting bound, permutation, ?_, ?_⟩
          · exact ⟨_, tailScope, .push head.realizes frontRealized, by simp only [head.realizes.append, wholeSame],
              by simp only [head.realizes.append, waitingSame]⟩
          · intro store receiving phases consumed
            rw [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_sequence,
              RecursiveRequirements.evaluate_prepend, RecursiveRequirements.evaluate_prepend]
            have headSame := RecursiveTransport.evaluate_transport (requirements := headReq) (store := store) (nextStore := store)
              (fun _ _ => rfl) (normalize_replaced (front := front) (capture := capture) (tail := tail)
                (input := inputType) (answer := answerType) (caller := caller) (tables := tables) (receiving := receiving) consumed)
            rw [← headSame, evaluation store receiving _ (RecursiveTransport.phases_spendAll_later owner consumed)]
  | live other otherInput otherAnswer savedFront savedScope front ihSaved ihFront => cases source with
      | @live other otherContract rights otherInput otherAnswer savedScope savedFront body nested savedScope savedBoundary restStack output demand requirements remaining restScope
          boundary outgoing incoming actual actualAction inputAnnotation answerAnnotation scope held savedOther otherInterface rest resume close bound =>
          obtain ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, capturedScope, waitingScope, capturedBoundary, saved, savedInterface, waiting, permutation, scopeSplit, evaluation⟩ := ihFront rest
          obtain ⟨frontScope, tailScope, frontRealized, wholeSame, waitingSame⟩ := scopeSplit
          have rebuilt := Segment.live actual actualAction inputAnnotation answerAnnotation scope held savedOther otherInterface waiting resume close bound
          refine ⟨capturedReq, capturedRecords, _, _, capturedScope, _, capturedBoundary, saved, savedInterface, rebuilt, ?_, ?_, ?_⟩
          · simpa only [List.cons_append, List.append_assoc] using
              move_records (prefixRecords := (⟨other, .resume⟩, ⟨otherContract.resumeDemand, body⟩) :: nested) permutation
          · exact ⟨_, tailScope, .live savedOther.realizes frontRealized,
              by simp only [SourceDependencyCapture.Scope.append, wholeSame],
              by simp only [SourceDependencyCapture.Scope.append, waitingSame]⟩
          · intro store receiving phases consumed
            simp only [RecursiveRequirements.evaluate_sequence, spendAll, evaluation store receiving phases consumed, evaluate_spent]
  | spent other answer savedScope front ih => cases source with
      | spent actual annotation scope rest bound =>
          obtain ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, capturedScope, waitingScope, capturedBoundary, saved, savedInterface, waiting, permutation, scopeSplit, evaluation⟩ := ih rest
          obtain ⟨frontScope, tailScope, frontRealized, wholeSame, waitingSame⟩ := scopeSplit
          refine ⟨capturedReq, capturedRecords, _, waitingRecords, capturedScope, _, capturedBoundary, saved, savedInterface, .spent actual annotation scope waiting bound, permutation, ?_, ?_⟩
          · exact ⟨_, tailScope, .spent frontRealized, by simp only [SourceDependencyCapture.Scope.append, wholeSame],
              by simp only [SourceDependencyCapture.Scope.append, waitingSame]⟩
          · intro store receiving phases consumed
            simp only [RecursiveRequirements.evaluate_sequence, spendAll, evaluation store receiving phases consumed, evaluate_spent]


/-- Resumption extracts the same enriched saved derivation and replaces only
the consumed live boundary. Existing record and phase transport proves the
one-shot accounting through every caller prefix, including other captures. -/
theorem replace_live
    (source : Segment operations policy contracts tables families actions world
      (front.append (.live owner inputType answerType capture caller tail)) input output demand requirements records wholeScope incoming outgoing)
    (known : contracts owner = some contract) (actionKnown : actions owner = some rights)
    (permitted : rights.resume = true) :
    ∃ (capturedRequirements : Requirements contract.resumeDemand) (capturedRecords : Store)
      (waitingRequirements : Requirements demand) (waitingRecords : Store) (capturedScope waitingScope : DependencyScope),
      Segment operations policy contracts tables families actions world capture contract.input contract.answer
        contract.resumeDemand capturedRequirements capturedRecords capturedScope [] contract.resumeEffects ∧
      Segment operations policy contracts tables families actions world (front.append (.spent owner answerType caller tail)) input output
        demand waitingRequirements waitingRecords waitingScope incoming outgoing ∧
      records.Perm ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (capturedRecords ++ waitingRecords)) ∧
      ∀ store receiving phases, phases owner = .consumed →
        evaluate store receiving phases waitingRequirements = evaluate store receiving phases requirements := by
  obtain ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, capturedScope, waitingScope,
    capturedBoundary, saved, savedInterface, waiting, permutation, scopeSplit, evaluation⟩ := extract_live source known actionKnown
  exact ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, capturedScope, waitingScope,
    saved.outgoing_weaken (savedInterface permitted), waiting, permutation, evaluation⟩

namespace Examples
open SourceDependencyAnnotations.Examples

def waitingFunction : PlainData :=
  ⟨.appArgument functionCode, .none, .unit, .unit, [], rfl⟩

/-- An actual waiting function frame retains cleanup nested in its lambda. -/
theorem waiting_function_source :
    Frame operations policy contracts (fun _ => []) (fun _ => []) [] (.plain waitingFunction)
      .unit .unit [] (.request [] cleanupRow) (.plain cleanupDependencies) allowed allowed :=
  .plain (.appArgument function_source (List.Subset.refl _)) .none rfl rfl

/-- Matching erased types cannot make that pending lambda's cleanup disappear. -/
theorem waiting_function_not_flat :
    ¬ Context operations policy contracts [] Environment.empty allowed .none
      (.appArgument functionCode) .unit .unit [] (.request [] cleanupRow) .pure := by
  intro source
  cases source with
  | appArgument function admitted => exact SourceDependencyAnnotations.lambda_cleanup_not_flat function

/-- The generic append proof retains the actual pending code's dependency and
its old requirement check even when exporting the stack into an empty tail. -/
theorem waiting_function_recomposed :
    ∃ requirements : Requirements [],
      Segment operations policy contracts (fun _ => []) (fun _ => []) (fun _ => none) []
        (.push (.plain waitingFunction) .nil) .unit .unit [] requirements []
        (.plain cleanupDependencies .nil) allowed allowed ∧
      ∀ store receiving phases, evaluate store receiving phases requirements =
        evaluate store receiving phases
          (.sequence ((Requirements.request [] cleanupRow).prepend []) (.request [] [])) := by
  have frame := waiting_function_source
  have first : Segment operations policy contracts (fun _ => []) (fun _ => []) (fun _ => none) []
      (.push (.plain waitingFunction) .nil) .unit .unit []
      (.sequence ((Requirements.request [] cleanupRow).prepend []) (.request [] [])) []
      (.plain cleanupDependencies .nil) allowed allowed :=
    .push frame (.nil (List.Subset.refl _)) (List.Subset.refl _)
  obtain ⟨requirements, joined, evaluation⟩ := segment_append first (.nil (List.Subset.refl allowed))
  refine ⟨requirements, joined, ?_⟩
  intro store receiving phases
  simpa only [OwnerPhases.ofStack, List.nil_append, RecursiveRecomposition.evaluate_empty,
    RecursiveRecomposition.merge_empty_right] using evaluation store receiving phases

end Examples

/-- Rich contract extension induces the existing erased contract relation,
so port and scope transport can be reused unchanged. -/
theorem erased_contract_extension {contracts nextContracts : Contracts} (extension : contracts.Extends nextContracts) :
    contracts.erase.Extends nextContracts.erase := by
  intro owner old known
  change (contracts owner).map Contract.erase = some old at known
  obtain ⟨rich, present, same⟩ := Option.map_eq_some_iff.mp known
  subst old
  exact SourceDependencyAnnotations.contract_erase_known (extension owner rich present)

theorem expression_transport
    (source : Expression operations policy contracts world allowed scope environment code result demand requirements dependencies)
    (extension : contracts.Extends nextContracts) (larger : world ⊆ nextWorld) :
    Expression operations policy nextContracts nextWorld allowed scope environment code result demand requirements dependencies :=
  SourceDependencyAnnotations.expression_world_weaken
    (SourceDependencyAnnotations.expression_extension source extension) larger

theorem body_transport (source : Body operations policy contracts world allowed scope environment code result header dependencies)
    (extension : contracts.Extends nextContracts) (larger : world ⊆ nextWorld) :
    Body operations policy nextContracts nextWorld allowed scope environment code result header dependencies := by
  cases source with
  | typed source rows => exact .typed (expression_transport source extension larger) rows
  | annotated source annotation rows => exact .annotated (expression_transport source extension larger) annotation rows

theorem offer_transport
    (source : Offer operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held disposes row dependencies)
    (extension : contracts.Extends nextContracts) (larger : world ⊆ nextWorld) :
    Offer operations policy nextContracts nextWorld environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held disposes row dependencies := by
  cases source with
  | unavailable => exact .unavailable
  | available resumeInterface closeInterface source =>
      apply Offer.available resumeInterface closeInterface
      intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
      exact body_transport (source owner contract (SourceDependencyAnnotations.extension_fresh extension fresh)
        inputSame answerSame resumeSame closeSame heldSame balance)
        (SourceDependencyAnnotations.insert_extension extension) larger

theorem declarations_transport
    (source : Declarations operations policy contracts world environment allowed requested answer clauses table dependencies)
    (extension : contracts.Extends nextContracts) (larger : world ⊆ nextWorld) :
    Declarations operations policy nextContracts nextWorld environment allowed requested answer clauses table dependencies := by
  induction clauses using Clauses.rec (motive_1 := fun _ => True) generalizing table dependencies
  case nil => cases source; exact .nil
  case cons operation parameter binder body rest ihBody ihRest => cases source with
    | cons known ordinary protectedMode rest =>
        exact .cons known (offer_transport ordinary extension larger) (offer_transport protectedMode extension larger) (ihRest rest)
  all_goals trivial

theorem Context.transport
    (source : Context operations policy contracts world environment allowed scope position input output demand requirements dependencies)
    (extension : contracts.Extends nextContracts) (larger : world ⊆ nextWorld) :
    Context operations policy nextContracts nextWorld environment allowed scope position input output demand requirements dependencies := by
  cases source with
  | pairLeft right => exact .pairLeft (expression_transport right extension larger)
  | pairRight left => exact .pairRight (expression_transport left extension larger)
  | appFunction argument admitted => exact .appFunction (expression_transport argument extension larger) admitted
  | appArgument function admitted => exact .appArgument (expression_transport function extension larger) admitted
  | bind body => exact .bind (expression_transport body extension larger)
  | branch yes no same => exact .branch (expression_transport yes extension larger) (expression_transport no extension larger) same
  | perform known admitted formed => exact .perform known admitted (ScopedPorts.in_world_mono formed larger)
  | resume known resolved permission admitted formed =>
      exact .resume (extension _ _ known) resolved permission admitted (ScopedPorts.in_world_mono formed larger)
  | cleanup body admitted => exact .cleanup (expression_transport body extension larger) admitted
  | resource body formed effectsBound admitted hidden =>
      exact .resource
        (fun identity fresh => expression_transport (body identity (fun member => fresh (larger member))) extension
          (ScopedExpressions.append_subset larger (List.Subset.refl _)))
        (ScopedPorts.in_world_mono formed larger) (effectsBound.trans larger) admitted
        (fun identity fresh => hidden identity (fun member => fresh (larger member)))

/-- Retain exact latent dependencies and source scope layers while extending
contracts or the resource world. Existing port transports handle the erased
interfaces; source typing is transported at the rich indices. -/
theorem Frame.transport
    (frame : Frame operations policy contracts tables families world entry input output demand requirements layer incoming outgoing)
    (extension : contracts.Extends nextContracts) (larger : world ⊆ nextWorld) :
    Frame operations policy nextContracts tables families nextWorld entry input output demand requirements layer incoming outgoing := by
  have ports := CoherentSourceTypes.Owners.port_contracts_extension (erased_contract_extension extension)
  have types := ScopedPorts.effect_extension_has_type_extension ports
  cases frame with
  | plain context scope inputAnnotation outputAnnotation =>
      exact .plain (context.transport extension larger) (ScopedPorts.effect_scope_extension scope ports) inputAnnotation outputAnnotation
  | handler scope annotation clauses coverage unique declarations capabilities modes =>
      exact .handler (ScopedPorts.effect_scope_known_extension scope ports) annotation
        (ScopedPorts.clauses_world_weaken clauses larger) coverage unique
        (declarations_transport declarations extension larger) capabilities modes
  | cell scope noEscape annotation interface =>
      exact .cell (ScopedPorts.scope_known_extension scope types) noEscape annotation
        (ScopedPorts.effect_frame_world_weaken (ScopedPorts.effect_frame_extension interface ports) larger)
  | armed scope callback annotation interface =>
      exact .armed (ScopedPorts.scope_known_extension scope types) (expression_transport callback extension larger) annotation
        (ScopedPorts.effect_frame_world_weaken (ScopedPorts.effect_frame_extension interface ports) larger)
  | running scope callback saved annotation interface =>
      exact .running (ScopedPorts.scope_known_extension scope types) (expression_transport callback extension larger)
        (expression_transport saved extension larger) annotation
        (ScopedPorts.effect_frame_world_weaken (ScopedPorts.effect_frame_extension interface ports) larger)
  | closing scope interface =>
      exact .closing (ScopedPorts.scope_known_extension scope types)
        (ScopedPorts.effect_frame_world_weaken (ScopedPorts.effect_frame_extension interface ports) larger)
  | retiring known interface =>
      exact .retiring (extension _ _ known)
        (ScopedPorts.effect_frame_world_weaken (ScopedPorts.effect_frame_extension interface ports) larger)

/-- One induction transports the whole rich forest, including historical
source in non-resumable captures, without changing demand/requirement records,
family annotations or shared effect boundaries. -/
theorem Segment.transport
    (source : Segment operations policy contracts tables families actions world
      stack input output demand requirements records dependencyScope incoming outgoing)
    (extension : contracts.Extends nextContracts) (permissions : Syntax.UsageExtension actions nextActions)
    (larger : world ⊆ nextWorld) :
    Segment operations policy nextContracts tables families nextActions nextWorld
      stack input output demand requirements records dependencyScope incoming outgoing := by
  have ports := CoherentSourceTypes.Owners.port_contracts_extension (erased_contract_extension extension)
  induction source with
  | nil bound => exact .nil bound
  | push head tail bound ih => exact .push (head.transport extension larger) ih bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live (extension _ _ known) (permissions _ _ actionKnown) inputAnnotation answerAnnotation
        (ScopedPorts.effect_scope_known_extension scope ports) held ihSaved savedBound ihTail resume close bound
  | spent known annotation scope tail bound ih =>
      exact .spent (extension _ _ known) annotation (ScopedPorts.effect_scope_known_extension scope ports) ih bound

end Ash.OneShot.SourceDependencyFrames

#print axioms Ash.OneShot.SourceDependencyFrames.value_erase
#print axioms Ash.OneShot.SourceDependencyFrames.function_latent_bound
#print axioms Ash.OneShot.SourceDependencyFrames.function_empty_latent
#print axioms Ash.OneShot.SourceDependencyFrames.body_erase
#print axioms Ash.OneShot.SourceDependencyFrames.offer_erase
#print axioms Ash.OneShot.SourceDependencyFrames.declarations_erase
#print axioms Ash.OneShot.SourceDependencyFrames.context_erase
#print axioms Ash.OneShot.SourceDependencyFrames.Frame.erase
#print axioms Ash.OneShot.SourceDependencyFrames.Frame.realizes

#print axioms Ash.OneShot.SourceDependencyFrames.erased_outgoing_weaken

#print axioms Ash.OneShot.SourceDependencyFrames.Segment.erase

#print axioms Ash.OneShot.SourceDependencyFrames.Segment.realizes

#print axioms Ash.OneShot.SourceDependencyFrames.Segment.input_weaken
#print axioms Ash.OneShot.SourceDependencyFrames.capture_segments

#print axioms Ash.OneShot.SourceDependencyFrames.segment_append

#print axioms Ash.OneShot.SourceDependencyFrames.capture_certificate
#print axioms Ash.OneShot.SourceDependencyFrames.capture_plan

#print axioms Ash.OneShot.SourceDependencyFrames.Examples.waiting_function_source

#print axioms Ash.OneShot.SourceDependencyFrames.Examples.waiting_function_not_flat

#print axioms Ash.OneShot.SourceDependencyFrames.Examples.waiting_function_recomposed

#print axioms Ash.OneShot.SourceDependencyFrames.Segment.outgoing_weaken

#print axioms Ash.OneShot.SourceDependencyFrames.replace_live

#print axioms Ash.OneShot.SourceDependencyFrames.erased_contract_extension

#print axioms Ash.OneShot.SourceDependencyFrames.expression_transport

#print axioms Ash.OneShot.SourceDependencyFrames.body_transport

#print axioms Ash.OneShot.SourceDependencyFrames.offer_transport

#print axioms Ash.OneShot.SourceDependencyFrames.declarations_transport

#print axioms Ash.OneShot.SourceDependencyFrames.Context.transport

#print axioms Ash.OneShot.SourceDependencyFrames.Frame.transport

#print axioms Ash.OneShot.SourceDependencyFrames.Segment.transport

#print axioms Ash.OneShot.SourceDependencyFrames.extract_live


namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations
open RecursiveRequirements (Requirements)

/-- Source evidence for the actual lexical machine. Ordinary frames retain
    their existing rich derivations. An unwinding callback has no saved value;
    internal close and retirement boundaries accept the abandoned answer type. -/
inductive LexicalFrame (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (families : Families) (world : List Nat) :
    ExecFrame → Value → Value → (demand : List Nat) → Requirements demand → (DependencyScope → DependencyScope) →
      List Instance → List Instance → Prop where
  | ordinary (source : Frame operations policy contracts tables families world
      entry input output demand requirements layer incoming outgoing) :
      LexicalFrame operations policy contracts tables families world entry input output demand requirements layer incoming outgoing
  | unwinding (scope : ScopedPorts.ScopeKnown contracts.erase.ports.types action.scope)
      (callback : ValueSummary operations policy contracts world Environment.empty [] action.action
        (.function .unit .unit action.requests latent dependencies))
      (annotation : result.erase.port = ScopedPorts.eraseType action.answer)
      (interface : ScopedPorts.EffectFrame operations.erase.ports contracts.erase.ports world (.armed action) incoming outgoing) :
      LexicalFrame operations policy contracts tables families world (.unwinding action) .unit result
        [] (.request [] []) .running incoming outgoing
  | closing (scope : ScopedPorts.EffectScopeKnown contracts.erase.ports caller) :
      LexicalFrame operations policy contracts tables families world (.closing identity caller) input .unit
        [] (.request [] []) .running effects effects
  | retiring (known : contracts owner = some contract) :
      LexicalFrame operations policy contracts tables families world (.retiring owner) input input
        [owner] (.retire owner) .running effects effects

/-- The input and output ports come from the same retained source derivation,
    including the non-Unit abandoned answer at an unwinding return point. -/
theorem LexicalFrame.ports
    (source : LexicalFrame operations policy contracts tables families world
      entry input output demand requirements layer incoming outgoing) :
    LexicalUnwind.FramePorts operations.erase.ports contracts.erase.ports.types world
      entry input.erase.port output.erase.port := by
  cases source with
  | ordinary frame =>
      have erased := DeclaredSourceFrames.frame_erase frame.erase.source
      obtain ⟨first, last⟩ := SourceTemplates.frame_annotations erased
      rw [first, last]
      exact .ordinary (SourceTemplates.frame_ports erased)
  | unwinding scope callback annotation interface =>
      rw [annotation]
      exact .unwinding scope ((DeclaredSourceValues.erase (value_erase callback)).ports .none)
  | closing scope => exact .closing (ScopedPorts.effect_scope_known_has_types scope)
  | retiring known => exact .retiring (SharedSourceSegments.types_lookup (contract_erase_known known))

/-- Only the effect interface uses the armed-frame projection. The port proof
    above, source derivation and physical protection retain the actual marker. -/
theorem LexicalFrame.interface
    (source : LexicalFrame operations policy contracts tables families world
      entry input output demand requirements layer incoming outgoing) :
    ScopedPorts.EffectFrame operations.erase.ports contracts.erase.ports world
      (LexicalUnwind.effectFrameView entry) incoming outgoing := by
  cases source with
  | ordinary frame =>
      have same : LexicalUnwind.effectFrameView entry = entry := by cases frame <;> rfl
      rw [same]
      exact frame.erase.interface
  | unwinding scope callback annotation interface => exact interface
  | closing scope => exact .closing scope
  | retiring known => exact .retiring (CoherentSourceTypes.Owners.ports_lookup (contract_erase_known known))

/-- Starting lexical cleanup reuses ordinary source application. Its latent
    body and effect annotations are retained verbatim, not flattened away. -/
theorem LexicalFrame.start_cleanup
    (source : LexicalFrame operations policy contracts tables families world
      (.armed action) input output demand requirements layer incoming outgoing) :
    ∃ latent dependencies,
      layer = .cleanup action.requests dependencies ∧
      Expression operations policy contracts world incoming .none Environment.empty
        (.app action.action .unit) .unit []
        (.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent)
        (.sequence .pure (.sequence .pure dependencies)) ∧
      LexicalFrame operations policy contracts tables families world (.unwinding action) .unit output
        [] (.request [] []) .running incoming outgoing := by
  cases source with
  | ordinary frame => cases frame with
      | armed scope callback annotation interface =>
          rename_i latent dependencies
          refine ⟨latent, dependencies, rfl, ?_, .unwinding scope callback annotation interface⟩
          cases interface with
          | armed saved callable admitted =>
              exact .app (Values.change_allowed callback action.closed.1 _) .unit admitted

/-- Returning Unit consumes this callback frame and exposes its original
    saved scope and answer interface for the next unwind step. -/
theorem LexicalFrame.finish_cleanup
    (source : LexicalFrame operations policy contracts tables families world
      (.unwinding action) input output demand requirements layer incoming outgoing) :
    input = .unit ∧ output.erase.port = ScopedPorts.eraseType action.answer ∧
      ScopedPorts.ScopeKnown contracts.erase.ports.types action.scope ∧ incoming = outgoing := by
  cases source with
  | ordinary impossible => cases impossible
  | unwinding scope callback annotation interface =>
      cases interface
      exact ⟨rfl, annotation, scope, rfl⟩

#print axioms Ash.OneShot.SourceDependencyFrames.LexicalFrame.ports
#print axioms Ash.OneShot.SourceDependencyFrames.LexicalFrame.interface
#print axioms Ash.OneShot.SourceDependencyFrames.LexicalFrame.start_cleanup
#print axioms Ash.OneShot.SourceDependencyFrames.LexicalFrame.finish_cleanup
end Ash.OneShot.SourceDependencyFrames


namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations
open RecursiveRequirements (Requirements Store)

/-- Retained source derivations for the lexical machine. The enriched values,
    requirement indices and dormant capture records are the existing ones;
    only the frame relation admits the actual unwinding return boundary. -/
inductive LexicalSegment (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (families : Families) (actions : Syntax.UsageTickets) (world : List Nat) :
    Stack → Value → Value → (demand : List Nat) → Requirements demand → Store → DependencyScope →
      List Instance → List Instance → Prop where
  | nil (bound : incoming ⊆ outgoing) :
      LexicalSegment operations policy contracts tables families actions world .nil result result [] (.request [] []) [] .nil incoming outgoing
  | push (head : LexicalFrame operations policy contracts tables families world entry input middle headDemand first layer inner outer)
      (tail : LexicalSegment operations policy contracts tables families actions world rest middle output tailDemand second records restScope outer outgoing)
      (bound : incoming ⊆ inner) :
      LexicalSegment operations policy contracts tables families actions world (.push entry rest) input output
        (headDemand ++ tailDemand) (.sequence (first.prepend (OwnerPhases.ofStack tables rest)) second) records (layer restScope) incoming outgoing
  | live (known : contracts owner = some contract) (actionKnown : actions owner = some rights)
      (inputAnnotation : contract.input.erase.port = ScopedPorts.eraseType inputType)
      (answerAnnotation : contract.answer.erase.port = ScopedPorts.eraseType answerType)
      (scope : ScopedPorts.EffectScopeKnown contracts.erase.ports caller)
      (held : contract.held = ProtectionContexts.protectedMode capture.erase)
      (saved : LexicalSegment operations policy contracts tables families actions world
        capture contract.input contract.answer contract.resumeDemand body nested savedScope [] savedBoundary)
      (savedBound : rights.resume = true → savedBoundary ⊆ contract.resumeEffects)
      (tail : LexicalSegment operations policy contracts tables families actions world rest contract.answer output
        demand requirements remaining restScope boundary outgoing)
      (resume : rights.resume = true → contract.resumeEffects ⊆ boundary)
      (close : rights.dispose = true → contract.closeEffects ⊆ boundary)
      (bound : incoming ⊆ boundary) :
      LexicalSegment operations policy contracts tables families actions world (.live owner inputType answerType capture caller rest)
        contract.answer output demand (.sequence (.spent owner) requirements)
        ((⟨owner, .resume⟩, ⟨contract.resumeDemand, body⟩) :: (nested ++ remaining)) (.live owner savedScope restScope) incoming outgoing
  | spent (known : contracts owner = some contract)
      (annotation : contract.answer.erase.port = ScopedPorts.eraseType answerType)
      (scope : ScopedPorts.EffectScopeKnown contracts.erase.ports caller)
      (tail : LexicalSegment operations policy contracts tables families actions world rest contract.answer output
        demand requirements records restScope boundary outgoing)
      (bound : incoming ⊆ boundary) :
      LexicalSegment operations policy contracts tables families actions world (.spent owner answerType caller rest) contract.answer output
        demand (.sequence (.spent owner) requirements) records (.spent owner restScope) incoming outgoing


theorem Segment.lexical
    (source : Segment operations policy contracts tables families actions world
      stack input output demand requirements records dependencyScope incoming outgoing) :
    LexicalSegment operations policy contracts tables families actions world
      stack input output demand requirements records dependencyScope incoming outgoing := by
  induction source with
  | nil bound => exact .nil bound
  | push head tail bound ih => exact .push (.ordinary head) ih bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live known actionKnown inputAnnotation answerAnnotation scope held ihSaved savedBound ihTail resume close bound
  | spent known annotation scope tail bound ih => exact .spent known annotation scope ih bound

theorem LexicalSegment.ports
    (source : LexicalSegment operations policy contracts tables families actions world
      stack input output demand requirements records dependencyScope incoming outgoing) :
    LexicalUnwind.StackPorts operations.erase.ports contracts.erase.ports.types world
      stack input.erase.port output.erase.port := by
  induction source with
  | nil bound => exact .nil
  | push head tail bound ih => exact .push head.ports ih
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      have lookup := SharedSourceSegments.types_lookup (contract_erase_known known)
      simp only [Contract.erase] at lookup
      rw [inputAnnotation, answerAnnotation] at lookup
      rw [inputAnnotation, answerAnnotation] at ihSaved
      rw [answerAnnotation] at ihTail ⊢
      exact .live lookup (ScopedPorts.effect_scope_known_has_types scope) ihSaved ihTail
  | spent known annotation scope tail bound ih =>
      have lookup := SharedSourceSegments.types_lookup (contract_erase_known known)
      simp only [Contract.erase] at lookup
      rw [annotation] at lookup ih ⊢
      exact .spent lookup (ScopedPorts.effect_scope_known_has_types scope) ih

/-- Permission-sensitive effect interfaces are reused: a dormant capture need
    not be resumable when the independently checked clause denies resumption. -/
theorem LexicalSegment.connected
    (source : LexicalSegment operations policy contracts tables families actions world
      stack input output demand requirements records dependencyScope incoming outgoing) :
    ScopedActionInterfaces.Connected operations.erase.ports contracts.erase.ports actions world
      (LexicalUnwind.effectView stack) incoming outgoing := by
  induction source with
  | nil bound => exact .nil bound
  | push head tail bound ih => exact .push head.interface ih bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live (CoherentSourceTypes.Owners.ports_lookup (contract_erase_known known)) actionKnown scope
        (fun used => ScopedActionInterfaces.output_weaken ihSaved (savedBound used)) ihTail resume close bound
  | spent known annotation scope tail bound ih =>
      exact .spent (CoherentSourceTypes.Owners.ports_lookup (contract_erase_known known)) scope ih bound

theorem LexicalSegment.capture_protection
    (source : LexicalSegment operations policy contracts tables families actions world
      stack input output demand requirements records dependencyScope incoming outgoing) :
    LexicalUnwind.CaptureProtection (fun owner => (contracts owner).map Contract.held) stack := by
  induction source with
  | nil => exact .nil
  | push head tail bound ih => exact .push ih
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live (by simp [known, held]) ihSaved ihTail
  | spent known annotation scope tail bound ih => exact .spent ih

/-- The same source stack proves ordered lookup on the actual scopes, even
    when a running cleanup return point occurs inside a captured continuation. -/
theorem LexicalSegment.provides_or_exports
    (source : LexicalSegment operations policy contracts tables families actions world
      stack input output demand requirements records dependencyScope incoming outgoing)
    (used : request ∈ incoming) :
    (∃ target, stack.erase.resolve request = some target) ∨ request ∈ outgoing := by
  simpa only [LexicalUnwind.effect_view_resolve] using ScopedActionInterfaces.provides_or_exports source.connected used


theorem LexicalFrame.realizes
    (source : LexicalFrame operations policy contracts tables families world
      entry input output demand requirements layer incoming outgoing) :
    SourceDependencyCapture.Frame tables families layer entry := by
  cases source with
  | ordinary frame => exact frame.realizes
  | unwinding => exact .unwinding
  | closing => exact .closing
  | retiring => exact .retiring

theorem LexicalSegment.realizes
    (source : LexicalSegment operations policy contracts tables families actions world
      stack input output demand requirements records dependencyScope incoming outgoing) :
    SourceDependencyCapture.Realizes tables families dependencyScope stack := by
  induction source with
  | nil => exact .nil
  | push head tail bound ih => exact .push head.realizes ih
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live ihSaved ihTail
  | spent known annotation scope tail bound ih => exact .spent ih

open ProtectionResiduals
open RecursiveRequirements (evaluate)
open OwnerPhaseTransitions (spendAll)
open RecursiveRecomposition (evaluate_empty evaluate_spent merge_empty_left)
variable {front tail : Stack}

theorem LexicalSegment.input_weaken
    (segment : LexicalSegment operations policy contracts tables families actions world stack input output demand requirements records dependencyScope incoming outgoing)
    (shrink : smaller ⊆ incoming) :
    LexicalSegment operations policy contracts tables families actions world stack input output demand requirements records dependencyScope smaller outgoing := by
  cases segment with
  | nil bound => exact .nil (List.Subset.trans shrink bound)
  | push head tail bound => exact .push head tail (List.Subset.trans shrink bound)
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound =>
      exact .live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close (List.Subset.trans shrink bound)
  | spent known annotation scope tail bound => exact .spent known annotation scope tail (List.Subset.trans shrink bound)

theorem lexical_segment_append
    (first : LexicalSegment operations policy contracts tables families actions world front input middle
      firstDemand firstRequirements firstRecords firstScope incoming boundary)
    (second : LexicalSegment operations policy contracts tables families actions world tail middle output
      secondDemand secondRequirements secondRecords secondScope boundary outgoing) :
    ∃ combined : Requirements (firstDemand ++ secondDemand),
      LexicalSegment operations policy contracts tables families actions world (front.append tail) input output
        (firstDemand ++ secondDemand) combined (firstRecords ++ secondRecords) (firstScope.append secondScope) incoming outgoing ∧
      ∀ store receiving phases,
        evaluate store receiving phases combined =
          merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) phases firstRequirements)
            (evaluate store receiving (spendAll phases firstDemand) secondRequirements) := by
  induction first generalizing output secondDemand secondRequirements secondRecords secondScope tail outgoing with
  | nil bound =>
      refine ⟨secondRequirements, second.input_weaken bound, ?_⟩
      intro store receiving phases
      simp only [evaluate_empty, spendAll, merge_empty_left]
  | push head rest bound ih =>
      obtain ⟨combined, source, evaluation⟩ := ih second
      rw [List.append_assoc]
      have rebuilt := LexicalSegment.push head source bound
      rw [← head.realizes.append] at rebuilt
      refine ⟨_, rebuilt, ?_⟩
      intro store receiving phases
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        OwnerPhases.stack_append, List.append_assoc, evaluation, PhaseRechecking.spendAll_append, merge_assoc]
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedInterface rest resume close bound ihSaved ihRest =>
      obtain ⟨combined, source, evaluation⟩ := ihRest second
      have rebuilt := LexicalSegment.live known actionKnown inputAnnotation answerAnnotation scope held saved savedInterface source resume close bound
      simp only [List.cons_append, List.append_assoc]
      refine ⟨_, rebuilt, ?_⟩
      intro store receiving phases
      simp only [RecursiveRequirements.evaluate_sequence, evaluate_spent, evaluation, spendAll, merge_assoc]
  | spent known annotation scope rest bound ih =>
      obtain ⟨combined, source, evaluation⟩ := ih second
      refine ⟨_, .spent known annotation scope source bound, ?_⟩
      intro store receiving phases
      simp only [RecursiveRequirements.evaluate_sequence, evaluate_spent, evaluation, spendAll, merge_assoc]


theorem lexical_capture_segments
    (cut : HandlerCut requested whole capture tail handler)
    (source : LexicalSegment operations policy contracts tables families actions world whole input output demand requirements records wholeScope incoming outgoing) :
    ∃ (answer : Value) (residual : List Instance) (capturedDemand tailDemand : List Nat)
      (capturedRequirements : Requirements capturedDemand) (tailRequirements : Requirements tailDemand)
      (capturedRecords tailRecords : Store) (capturedScope tailScope : DependencyScope),
      answer.erase.port = ScopedPorts.eraseType handler.answer ∧ Frame operations policy contracts tables families world (.handler handler) answer answer [] (.request [] [])
        (.handler handler.effectInst (tables handler) (families handler)) (handler.effectInst :: residual) residual ∧
      LexicalSegment operations policy contracts tables families actions world capture input answer capturedDemand capturedRequirements capturedRecords capturedScope incoming residual ∧
      LexicalSegment operations policy contracts tables families actions world tail answer output tailDemand tailRequirements tailRecords tailScope residual outgoing ∧
      wholeScope = capturedScope.append tailScope ∧
      demand = capturedDemand ++ tailDemand ∧ records = capturedRecords ++ tailRecords ∧
      (∀ operation, SourceDependencyCapture.select requested operation wholeScope =
        SourceDependencyCapture.chosen operation (tables handler) (families handler) capturedScope tailScope) ∧
      ∀ store receiving before, evaluate store receiving before requirements =
        merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) before capturedRequirements)
          (evaluate store receiving (spendAll before capturedDemand) tailRequirements) := by
  induction cut generalizing input demand requirements records wholeScope incoming with
  | hit handler tail same => cases source with
    | push current rest bound => cases current with
      | ordinary current => cases current with
        | handler scope annotation clauses coverage unique declarations capabilities modes =>
            have frame := Frame.handler scope annotation clauses coverage unique declarations capabilities modes
            refine ⟨_, _, [], _, _, _, [], _, _, _, annotation, frame,
              .push (.ordinary frame) (.nil (List.Subset.refl _)) bound, rest, rfl, rfl, rfl, ?_, ?_⟩
            · intro operation
              simp only [SourceDependencyCapture.select, if_pos same.symm, SourceDependencyCapture.chosen]
              rfl
            intro store receiving before
            simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
              RecursiveRecomposition.evaluate_empty, spendAll, RecursiveRecomposition.merge_empty_left]
  | push entry rest cap tail handler miss next ih => cases source with
    | push current rest bound =>
        obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
          annotation, selected, saved, outside, sameScope, sameDemand, sameRecords, selection, evaluation⟩ := ih rest
        refine ⟨answer, residual, _, tailDemand, _, tailReq, capRecords, tailRecords, _, tailScope, annotation, selected, .push current saved bound, outside,
          by rw [current.realizes.append, ← sameScope],
          by simp only [sameDemand, List.append_assoc], sameRecords, ?_, ?_⟩
        · intro operation
          rw [current.realizes.select_miss miss, selection operation, SourceDependencyCapture.chosen_prepend]
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, evaluation,
          handler_cut_reconstructs next, OwnerPhases.stack_append, List.append_assoc,
          PhaseRechecking.spendAll_append, merge_assoc]
  | live owner inputType answerType savedScope caller rest cap tail handler next ih => cases source with
    | live known actionKnown inputAnnotation answerAnnotation scopeKnown held historical savedInterface rest resume close bound =>
        obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
          annotation, selected, saved, outside, sameScope, sameDemand, sameRecords, selection, evaluation⟩ := ih rest
        refine ⟨answer, residual, capDemand, tailDemand, _, tailReq, _, tailRecords, _, tailScope, annotation, selected,
          .live known actionKnown inputAnnotation answerAnnotation scopeKnown held historical savedInterface saved resume close bound, outside,
          by simp only [SourceDependencyCapture.Scope.append, ← sameScope], sameDemand, ?_, ?_, ?_⟩
        · simp only [sameRecords, List.cons_append, List.append_assoc]
        · intro operation
          rw [SourceDependencyCapture.select, selection operation, SourceDependencyCapture.chosen_prepend]
        · intro store receiving before
          simp only [RecursiveRequirements.evaluate_sequence, evaluation, RecursiveRecomposition.evaluate_spent,
            spendAll, merge_assoc]
  | spent owner answerType caller rest cap tail handler next ih => cases source with
    | spent known answerAnnotation scopeKnown rest bound =>
        obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
          annotation, selected, saved, outside, sameScope, sameDemand, sameRecords, selection, evaluation⟩ := ih rest
        refine ⟨answer, residual, capDemand, tailDemand, _, tailReq, capRecords, tailRecords, _, tailScope, annotation, selected,
          .spent known answerAnnotation scopeKnown saved bound, outside, by simp only [SourceDependencyCapture.Scope.append, ← sameScope], sameDemand, sameRecords, ?_, ?_⟩
        · intro operation
          rw [SourceDependencyCapture.select, selection operation, SourceDependencyCapture.chosen_prepend]
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_sequence, evaluation, RecursiveRecomposition.evaluate_spent,
          spendAll, merge_assoc]


/-- Cleanup entry retains the entire typed suffix, including dormant source
    captures. Its actual callback application uses the frame's own effect row;
    no source derivation or safety assertion for the successor is a premise. -/
theorem LexicalSegment.start_cleanup
    (source : LexicalSegment operations policy contracts tables families actions world
      (.push (.armed action) rest) input output demand requirements records dependencyScope incoming outgoing) :
    ∃ allowed latent dependencies, ∃ nextRequirements : Requirements demand, ∃ nextScope suffixScope,
      dependencyScope = .cleanup action.requests dependencies suffixScope ∧
      nextScope = .running suffixScope ∧
      Expression operations policy contracts world allowed .none Environment.empty
        (.app action.action .unit) .unit []
        (.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent)
        (.sequence .pure (.sequence .pure dependencies)) ∧
      LexicalSegment operations policy contracts tables families actions world
        (.push (.unwinding action) rest) .unit output demand nextRequirements records nextScope allowed outgoing := by
  cases source with
  | push frame rest bound => cases frame with
    | ordinary frame => cases frame with
      | armed scope callback annotation interface =>
          have entry := LexicalFrame.start_cleanup (tables := tables) (families := families) (.ordinary (Frame.armed scope callback annotation interface))
          obtain ⟨latent, dependencies, sameLayer, expression, marker⟩ := entry
          exact ⟨_, latent, dependencies, _, _, _, congrFun sameLayer _, rfl, expression,
            .push marker rest (List.Subset.refl _)⟩

/-- After the callback returns, its marker exposes the same retained source
    suffix and saved lexical scope. The suffix is not re-inferred or retyped. -/
theorem LexicalSegment.finish_cleanup
    (source : LexicalSegment operations policy contracts tables families actions world
      (.push (.unwinding action) rest) input output demand requirements records dependencyScope incoming outgoing) :
    ScopedPorts.ScopeKnown contracts.erase.ports.types action.scope ∧
      ∃ nextInput, ∃ nextRequirements : Requirements demand, ∃ nextScope boundary,
        LexicalSegment operations policy contracts tables families actions world
          rest nextInput output demand nextRequirements records nextScope boundary outgoing := by
  cases source with
  | push frame rest bound => cases frame with
    | ordinary impossible => cases impossible
    | unwinding scope callback annotation interface => exact ⟨scope, _, _, _, _, rest⟩

#print axioms Ash.OneShot.SourceDependencyFrames.LexicalSegment.start_cleanup
#print axioms Ash.OneShot.SourceDependencyFrames.LexicalSegment.finish_cleanup

#print axioms Ash.OneShot.SourceDependencyFrames.LexicalFrame.realizes
#print axioms Ash.OneShot.SourceDependencyFrames.LexicalSegment.realizes
#print axioms Ash.OneShot.SourceDependencyFrames.LexicalSegment.input_weaken
#print axioms Ash.OneShot.SourceDependencyFrames.lexical_segment_append
#print axioms Ash.OneShot.SourceDependencyFrames.lexical_capture_segments
#print axioms Ash.OneShot.SourceDependencyFrames.Segment.lexical
#print axioms Ash.OneShot.SourceDependencyFrames.LexicalSegment.ports
#print axioms Ash.OneShot.SourceDependencyFrames.LexicalSegment.connected
#print axioms Ash.OneShot.SourceDependencyFrames.LexicalSegment.capture_protection
#print axioms Ash.OneShot.SourceDependencyFrames.LexicalSegment.provides_or_exports
end Ash.OneShot.SourceDependencyFrames


namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations
open RecursiveRequirements (Requirements Store evaluate)
open OwnerPhaseTransitions (spendAll)
open RecursiveRecomposition (normalize_replaced move_records evaluate_spent)
variable {front tail capture : Stack}

theorem LexicalSegment.outgoing_weaken
    (segment : LexicalSegment operations policy contracts tables families actions world stack input output demand requirements records dependencyScope incoming outgoing)
    (grow : outgoing ⊆ larger) :
    LexicalSegment operations policy contracts tables families actions world stack input output demand requirements records dependencyScope incoming larger := by
  induction segment with
  | nil bound => exact .nil (List.Subset.trans bound grow)
  | push head tail bound ih => exact .push head (ih grow) bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound (ihTail grow) resume close bound
  | spent known annotation scope tail bound ih => exact .spent known annotation scope (ih grow) bound

theorem lexical_extract_live
    (source : LexicalSegment operations policy contracts tables families actions world
      (front.append (.live owner inputType answerType capture caller tail)) input output demand requirements records wholeScope incoming outgoing)
    (known : contracts owner = some contract) (actionKnown : actions owner = some rights) :
    ∃ (capturedRequirements : Requirements contract.resumeDemand) (capturedRecords : Store)
      (waitingRequirements : Requirements demand) (waitingRecords : Store) (capturedScope waitingScope : DependencyScope) (capturedBoundary : List Instance),
      LexicalSegment operations policy contracts tables families actions world capture contract.input contract.answer
        contract.resumeDemand capturedRequirements capturedRecords capturedScope [] capturedBoundary ∧
      (rights.resume = true → capturedBoundary ⊆ contract.resumeEffects) ∧
      LexicalSegment operations policy contracts tables families actions world (front.append (.spent owner answerType caller tail)) input output
        demand waitingRequirements waitingRecords waitingScope incoming outgoing ∧
      records.Perm ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (capturedRecords ++ waitingRecords)) ∧
      (∃ frontScope tailScope, SourceDependencyCapture.Realizes tables families frontScope front ∧
        wholeScope = frontScope.append (.live owner capturedScope tailScope) ∧
        waitingScope = frontScope.append (.spent owner tailScope)) ∧
      ∀ store receiving phases, phases owner = .consumed →
        evaluate store receiving phases waitingRequirements = evaluate store receiving phases requirements := by
  induction front generalizing input demand requirements records wholeScope incoming with
  | nil => cases source with
      | live actual actualAction inputAnnotation answerAnnotation scope held saved savedInterface rest resume close bound =>
          have same := Option.some.inj (actual.symm.trans known)
          have sameRights := Option.some.inj (actualAction.symm.trans actionKnown)
          cases same
          cases sameRights
          refine ⟨_, _, _, _, _, _, _, saved, savedInterface, .spent known answerAnnotation scope rest bound, .refl _, ⟨.nil, _, .nil, rfl, rfl⟩, ?_⟩
          intros; rfl
  | push frame front ih => cases source with
      | @push entry input middle headDemand headReq layer inner outer restStack output tailDemand tailReq records restScope outgoing incoming head rest bound =>
          obtain ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, capturedScope, waitingScope, capturedBoundary, saved, savedInterface, waiting, permutation, scopeSplit, evaluation⟩ := ih rest
          obtain ⟨frontScope, tailScope, frontRealized, wholeSame, waitingSame⟩ := scopeSplit
          refine ⟨capturedReq, capturedRecords, _, waitingRecords, capturedScope, _, capturedBoundary, saved, savedInterface, .push head waiting bound, permutation, ?_, ?_⟩
          · exact ⟨_, tailScope, .push head.realizes frontRealized, by simp only [head.realizes.append, wholeSame],
              by simp only [head.realizes.append, waitingSame]⟩
          · intro store receiving phases consumed
            rw [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_sequence,
              RecursiveRequirements.evaluate_prepend, RecursiveRequirements.evaluate_prepend]
            have headSame := RecursiveTransport.evaluate_transport (requirements := headReq) (store := store) (nextStore := store)
              (fun _ _ => rfl) (normalize_replaced (front := front) (capture := capture) (tail := tail)
                (input := inputType) (answer := answerType) (caller := caller) (tables := tables) (receiving := receiving) consumed)
            rw [← headSame, evaluation store receiving _ (RecursiveTransport.phases_spendAll_later owner consumed)]
  | live other otherInput otherAnswer savedFront savedScope front ihSaved ihFront => cases source with
      | @live other otherContract rights otherInput otherAnswer savedScope savedFront body nested savedScope savedBoundary restStack output demand requirements remaining restScope
          boundary outgoing incoming actual actualAction inputAnnotation answerAnnotation scope held savedOther otherInterface rest resume close bound =>
          obtain ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, capturedScope, waitingScope, capturedBoundary, saved, savedInterface, waiting, permutation, scopeSplit, evaluation⟩ := ihFront rest
          obtain ⟨frontScope, tailScope, frontRealized, wholeSame, waitingSame⟩ := scopeSplit
          have rebuilt := LexicalSegment.live actual actualAction inputAnnotation answerAnnotation scope held savedOther otherInterface waiting resume close bound
          refine ⟨capturedReq, capturedRecords, _, _, capturedScope, _, capturedBoundary, saved, savedInterface, rebuilt, ?_, ?_, ?_⟩
          · simpa only [List.cons_append, List.append_assoc] using
              move_records (prefixRecords := (⟨other, .resume⟩, ⟨otherContract.resumeDemand, body⟩) :: nested) permutation
          · exact ⟨_, tailScope, .live savedOther.realizes frontRealized,
              by simp only [SourceDependencyCapture.Scope.append, wholeSame],
              by simp only [SourceDependencyCapture.Scope.append, waitingSame]⟩
          · intro store receiving phases consumed
            simp only [RecursiveRequirements.evaluate_sequence, spendAll, evaluation store receiving phases consumed, evaluate_spent]
  | spent other answer savedScope front ih => cases source with
      | spent actual annotation scope rest bound =>
          obtain ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, capturedScope, waitingScope, capturedBoundary, saved, savedInterface, waiting, permutation, scopeSplit, evaluation⟩ := ih rest
          obtain ⟨frontScope, tailScope, frontRealized, wholeSame, waitingSame⟩ := scopeSplit
          refine ⟨capturedReq, capturedRecords, _, waitingRecords, capturedScope, _, capturedBoundary, saved, savedInterface, .spent actual annotation scope waiting bound, permutation, ?_, ?_⟩
          · exact ⟨_, tailScope, .spent frontRealized, by simp only [SourceDependencyCapture.Scope.append, wholeSame],
              by simp only [SourceDependencyCapture.Scope.append, waitingSame]⟩
          · intro store receiving phases consumed
            simp only [RecursiveRequirements.evaluate_sequence, spendAll, evaluation store receiving phases consumed, evaluate_spent]


/-- Resumption extracts the same enriched saved derivation and replaces only
the consumed live boundary. Existing record and phase transport proves the
one-shot accounting through every caller prefix, including other captures. -/
theorem lexical_replace_live
    (source : LexicalSegment operations policy contracts tables families actions world
      (front.append (.live owner inputType answerType capture caller tail)) input output demand requirements records wholeScope incoming outgoing)
    (known : contracts owner = some contract) (actionKnown : actions owner = some rights)
    (permitted : rights.resume = true) :
    ∃ (capturedRequirements : Requirements contract.resumeDemand) (capturedRecords : Store)
      (waitingRequirements : Requirements demand) (waitingRecords : Store) (capturedScope waitingScope : DependencyScope),
      LexicalSegment operations policy contracts tables families actions world capture contract.input contract.answer
        contract.resumeDemand capturedRequirements capturedRecords capturedScope [] contract.resumeEffects ∧
      LexicalSegment operations policy contracts tables families actions world (front.append (.spent owner answerType caller tail)) input output
        demand waitingRequirements waitingRecords waitingScope incoming outgoing ∧
      records.Perm ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (capturedRecords ++ waitingRecords)) ∧
      ∀ store receiving phases, phases owner = .consumed →
        evaluate store receiving phases waitingRequirements = evaluate store receiving phases requirements := by
  obtain ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, capturedScope, waitingScope,
    capturedBoundary, saved, savedInterface, waiting, permutation, scopeSplit, evaluation⟩ := lexical_extract_live source known actionKnown
  exact ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, capturedScope, waitingScope,
    saved.outgoing_weaken (savedInterface permitted), waiting, permutation, evaluation⟩

/-- A source-typed resumption constructs the actual checked use transition
    and retains rich source typing for both the resumed value and recomposed
    stack. Reentry bounds remain a finite pre-step check, not a safe-successor
    premise. Contextual requirement satisfaction is a separate invariant. -/
theorem lexical_resume_source
    (current : Expression operations policy contracts world allowed runtimeScope Environment.empty
      (.resume binder value) input currentDemand currentRequirements dependencies)
    (pending : LexicalSegment operations policy contracts tables families actions world
      (front.append (.live owner inputType answerType capture caller tail)) input output
      pendingDemand pendingRequirements records wholeScope allowed outgoing)
    (known : contracts owner = some contract) (actionKnown : actions owner = some rights)
    (resolved : runtimeScope.resolve binder = some owner)
    (isValue : value.IsValue) (permitted : rights.resume = true)
    (bounds : LexicalUnwind.ReentryBounds front capture tail (LexicalUnwind.returnMode capture .ordinary)) :
    ∃ capturedRequirements : Requirements contract.resumeDemand,
    ∃ nextRequirements : Requirements (contract.resumeDemand ++ pendingDemand),
    ∃ nextRecords nextScope,
      currentDemand = owner :: contract.resumeDemand ∧
      ValueSummary operations policy contracts world Environment.empty [] value contract.input ∧
      LexicalSegment operations policy contracts tables families actions world
        (capture.append (front.append (.spent owner answerType caller tail))) contract.input output
        (contract.resumeDemand ++ pendingDemand) nextRequirements nextRecords nextScope [] outgoing ∧
      records.Perm ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: nextRecords) ∧
      LexicalUnwind.UseTransition
        (.eval ⟨.resume binder value, runtimeScope, front.append (.live owner inputType answerType capture caller tail)⟩)
        (.eval ⟨value, runtimeScope, capture.append (front.append (.spent owner answerType caller tail))⟩)
        [] [.ticket owner] := by
  cases current with
  | resume currentKnown currentResolved permission operand admitted formed =>
      cases Option.some.inj (currentResolved.symm.trans resolved)
      cases Option.some.inj (currentKnown.symm.trans known)
      have empty := SourceTemplates.expression_value_demand
        (DeclaredSources.expression_erase (expression_erase operand)) isValue
      have payload := Values.change_allowed (Values.summary operand isValue) isValue []
      have closed := ScopedPorts.typed_value_closed
        ((DeclaredSourceValues.erase (value_erase payload)).ports .none) isValue
      obtain ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, capturedScope, waitingScope,
        saved, waiting, permutation, evaluation⟩ := lexical_replace_live pending known actionKnown permitted
      obtain ⟨combined, source, calculation⟩ := lexical_segment_append saved (waiting.input_weaken admitted)
      refine ⟨capturedReq, combined, _, _, ?_, payload, source, permutation, ?_⟩
      · simp only [empty, List.nil_append]
      · exact .resume binder owner runtimeScope caller inputType answerType front capture tail value closed resolved bounds

#print axioms Ash.OneShot.SourceDependencyFrames.lexical_resume_source
#print axioms Ash.OneShot.SourceDependencyFrames.LexicalSegment.outgoing_weaken
#print axioms Ash.OneShot.SourceDependencyFrames.lexical_extract_live
#print axioms Ash.OneShot.SourceDependencyFrames.lexical_replace_live
end Ash.OneShot.SourceDependencyFrames


namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution SourceDependencyAnnotations
/-- Fresh continuation contracts and resources retain the original callback
    and frame annotations. Ordinary source transport is reused unchanged. -/
theorem LexicalFrame.transport
    (source : LexicalFrame operations policy contracts tables families world
      entry input output demand requirements layer incoming outgoing)
    (extension : contracts.Extends nextContracts) (larger : world ⊆ nextWorld) :
    LexicalFrame operations policy nextContracts tables families nextWorld
      entry input output demand requirements layer incoming outgoing := by
  have ports := CoherentSourceTypes.Owners.port_contracts_extension (erased_contract_extension extension)
  have types := ScopedPorts.effect_extension_has_type_extension ports
  cases source with
  | ordinary frame => exact .ordinary (frame.transport extension larger)
  | unwinding scope callback annotation interface =>
      exact .unwinding (ScopedPorts.scope_known_extension scope types)
        (expression_transport callback extension larger) annotation
        (ScopedPorts.effect_frame_world_weaken (ScopedPorts.effect_frame_extension interface ports) larger)
  | closing scope => exact .closing (ScopedPorts.effect_scope_known_extension scope ports)
  | retiring known => exact .retiring (extension _ _ known)

theorem LexicalSegment.transport
    (source : LexicalSegment operations policy contracts tables families actions world
      stack input output demand requirements records dependencyScope incoming outgoing)
    (extension : contracts.Extends nextContracts) (permissions : Syntax.UsageExtension actions nextActions)
    (larger : world ⊆ nextWorld) :
    LexicalSegment operations policy nextContracts tables families nextActions nextWorld
      stack input output demand requirements records dependencyScope incoming outgoing := by
  have ports := CoherentSourceTypes.Owners.port_contracts_extension (erased_contract_extension extension)
  induction source with
  | nil bound => exact .nil bound
  | push head tail bound ih => exact .push (head.transport extension larger) ih bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live (extension _ _ known) (permissions _ _ actionKnown) inputAnnotation answerAnnotation
        (ScopedPorts.effect_scope_known_extension scope ports) held ihSaved savedBound ihTail resume close bound
  | spent known annotation scope tail bound ih =>
      exact .spent (extension _ _ known) annotation (ScopedPorts.effect_scope_known_extension scope ports) ih bound

#print axioms Ash.OneShot.SourceDependencyFrames.LexicalFrame.transport
#print axioms Ash.OneShot.SourceDependencyFrames.LexicalSegment.transport
end Ash.OneShot.SourceDependencyFrames


namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations
open RecursiveRequirements (Requirements evaluate)
open OwnerPhaseTransitions (spendAll)
open RecursiveContexts (evaluate_request)

/-- Exact dependency-tree changes made by the strict evaluation contexts.
    Only already evaluated value prefixes may disappear; latent bodies remain. -/
inductive FocusDependencies : Dependencies → Dependencies → Dependencies → Prop where
  | direct : FocusDependencies (.sequence child rest) child rest
  | purePair : FocusDependencies .pure .pure .pure
  | leftValue (silent : value.Silent) : FocusDependencies (.sequence value child) child .pure
  | functionValue (silent : value.Silent) :
      FocusDependencies (.sequence value (.sequence child rest)) child rest

/-- A pure source summary is independent of the active continuation binder.
    Its latent function body remains checked under its original source rule. -/
theorem pure_at_scope
    (source : Expression operations policy contracts world allowed originalScope environment
      code value demand requirements dependencies) (pure : dependencies = .pure) :
    Expression operations policy contracts world allowed scope environment code value [] (.request [] []) .pure := by
  induction source using Expression.rec
      (motive_2 := fun _ _ _ _ _ _ _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ _ _ _ _ => True) with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | «variable» known formed => exact .variable known formed
  | lambda body outward formed latentBound ih => exact .lambda body outward formed latentBound
  | purePair left right ihLeft ihRight => exact .purePair (ihLeft rfl) (ihRight rfl)
  | pair | app | bind | branch | perform | handler | resume | discard | cleanup | resource => cases pure
  | typed | annotated | unavailable | available | nil | cons => trivial

/-- Plugging retains enriched values and latent dependencies. Requirement
    evaluation reuses the established context equations. -/
theorem rich_context_plug
    (context : Context operations policy contracts world environment allowed scope position input output restDemand rest restDependencies)
    (child : Expression operations policy contracts world allowed scope environment code input childDemand current childDependencies) :
    ∃ combined : Requirements (childDemand ++ restDemand), ∃ dependencies,
      Expression operations policy contracts world allowed scope environment (position.plug code) output
        (childDemand ++ restDemand) combined dependencies ∧
      FocusDependencies dependencies childDependencies restDependencies ∧
      ∀ store receiving before, evaluate store receiving before combined =
        merge (evaluate store receiving before current) (evaluate store receiving (spendAll before childDemand) rest) := by
  cases context with
  | pairLeft right => exact ⟨_, _, .pair child right, .direct, fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
  | pairRight left =>
      rw [List.append_nil]
      refine ⟨_, _, .pair (pure_at_scope left rfl) child, .leftValue .pure, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_empty, spendAll,
        RecursiveRecomposition.merge_empty_left, RecursiveRecomposition.merge_empty_right]
  | appFunction argument admitted =>
      refine ⟨_, _, .app child argument admitted, .direct, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence, PhaseRechecking.spendAll_append, merge_assoc]
  | appArgument function admitted =>
      rw [List.append_nil]
      refine ⟨_, _, .app (pure_at_scope function rfl) child admitted, .functionValue .pure, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_empty,
        spendAll, List.nil_append, RecursiveRecomposition.merge_empty_left, evaluate_request]
  | bind body => exact ⟨_, _, .bind child body, .direct, fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
  | branch yes no same => exact ⟨_, _, .branch child yes no same, .direct, fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
  | perform known admitted formed =>
      rw [List.append_nil]
      refine ⟨_, _, .perform known admitted child formed, .direct, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, evaluate_request, List.nil_append]
  | resource body formed effectsBound admitted hidden =>
      exact ⟨_, _, .resource child body formed effectsBound admitted hidden, .direct,
        fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
  | resume known resolved permission admitted formed =>
      exact ⟨_, _, .resume known resolved permission child admitted formed, .direct, fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
  | cleanup body admitted =>
      refine ⟨_, _, .cleanup child body admitted, .direct, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence, PhaseRechecking.spendAll_append, merge_assoc]

/-- The ten strict evaluation positions retain the child's and waiting
    context's rich source annotations. The original requirement evaluation
    splits by the same equations used for ordinary declared source contexts. -/
theorem rich_focus_decompose
    (source : Expression operations policy contracts world allowed scope environment whole output demand requirements dependencies)
    (focus : Focus whole child position) :
    ∃ (input : Value) (childDemand restDemand : List Nat) (current : Requirements childDemand) (rest : Requirements restDemand) (currentDependencies restDependencies : Dependencies),
      Expression operations policy contracts world allowed scope environment child input childDemand current currentDependencies ∧
      Context operations policy contracts world environment allowed scope position input output restDemand rest restDependencies ∧
      demand = childDemand ++ restDemand ∧
      FocusDependencies dependencies currentDependencies restDependencies ∧
      RequirementPath current requirements [] ∧
      ∀ store receiving before, evaluate store receiving before requirements =
        merge (evaluate store receiving before current) (evaluate store receiving (spendAll before childDemand) rest) := by
  cases source with
  | handler => cases focus
  | unit | boolean | integer | reference | «variable» => cases focus
  | lambda => cases focus
  | purePair left right => cases focus with
    | pairLeft =>
        refine ⟨_, [], [], _, _, _, _, left, .pairLeft right, rfl, .purePair, .here, ?_⟩
        intro store receiving before
        simp only [RecursiveRecomposition.evaluate_empty, merge, List.nil_append]
    | pairRight isValue notValue =>
        refine ⟨_, [], [], _, _, _, _, right, .pairRight (Values.summary left isValue), rfl, .purePair, .here, ?_⟩
        intro store receiving before
        simp only [RecursiveRecomposition.evaluate_empty, merge, List.nil_append]
  | pair left right => cases focus with
    | pairLeft => exact ⟨_, _, _, _, _, _, _, left, .pairLeft right, rfl, .direct, .first .here, fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
    | pairRight isValue notValue =>
        have empty := SourceTemplates.expression_value_demand (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase left)) isValue
        subst_vars
        refine ⟨_, _, [], _, _, _, _, right, .pairRight (Values.summary left isValue), by simp, .leftValue (value_silent left isValue), .second .here, ?_⟩
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase left)) isValue,
          RecursiveRecomposition.evaluate_empty, spendAll, RecursiveRecomposition.merge_empty_left, RecursiveRecomposition.merge_empty_right]
  | app function argument admitted => cases focus with
    | appFunction =>
        refine ⟨_, _, _, _, _, _, _, function, .appFunction argument admitted, rfl, .direct, .body (.first .here), ?_⟩
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence, PhaseRechecking.spendAll_append, merge_assoc]
    | appArgument isValue notValue =>
        have empty := SourceTemplates.expression_value_demand (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase function)) isValue
        subst_vars
        refine ⟨_, _, [], _, _, _, _, argument, .appArgument (Values.summary function isValue) admitted, by simp, .functionValue (value_silent function isValue), .body (.second .here), ?_⟩
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence,
          RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase function)) isValue, spendAll, List.nil_append,
          RecursiveRecomposition.merge_empty_left, evaluate_request]
  | bind initializer body => cases focus with
    | bind => exact ⟨_, _, _, _, _, _, _, initializer, .bind body, rfl, .direct, .first .here, fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
  | branch condition yes no same => cases focus with
    | branch => exact ⟨_, _, _, _, _, _, _, condition, .branch yes no same, rfl, .direct, .first .here, fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
  | perform known admitted operand formed => cases focus with
    | perform =>
        refine ⟨_, _, [], _, _, _, _, operand, .perform known admitted formed, by simp, .direct, .body .here, ?_⟩
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_emit, evaluate_request, List.nil_append]
  | resource initializer body formed effectsBound admitted hidden => cases focus with
    | resource notValue =>
        exact ⟨_, _, _, _, _, _, _, initializer, .resource body formed effectsBound admitted hidden,
          rfl, .direct, .first .here, fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
  | resume known resolved permission operand admitted formed => cases focus with
    | resume => exact ⟨_, _, _, _, _, _, _, operand, .resume known resolved permission admitted formed, rfl, .direct, .first .here,
        fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
  | discard => cases focus
  | cleanup callback body admitted => cases focus with
    | cleanup =>
        refine ⟨_, _, _, _, _, _, _, callback, .cleanup body admitted, rfl, .direct, .body (.first .here), ?_⟩
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence, PhaseRechecking.spendAll_append, merge_assoc]


/-- Source focus chooses the actual runtime annotations once, then uses
    that same frame for rich source typing, effects and checked execution. -/
theorem lexical_focus_source
    (current : Expression operations policy contracts world allowed runtimeScope Environment.empty
      whole input currentDemand currentRequirements dependencies)
    (pending : LexicalSegment operations policy contracts tables families actions world
      stack input output pendingDemand pendingRequirements records dependencyScope allowed outgoing)
    (scopeTyped : ScopedPorts.EffectScope contracts.erase.ports runtimeScope ticket)
    (position : Focus whole child context) :
    ∃ (plain : PlainData) (nextInput : Value) (childDemand restDemand : List Nat),
    ∃ childRequirements : Requirements childDemand,
    ∃ nextRequirements : Requirements (restDemand ++ pendingDemand),
    ∃ childDependencies restDependencies,
      plain.context = context ∧ plain.scope = runtimeScope ∧
      Expression operations policy contracts world allowed runtimeScope Environment.empty
        child nextInput childDemand childRequirements childDependencies ∧
      LexicalSegment operations policy contracts tables families actions world
        (.push (.plain plain) stack) nextInput output (restDemand ++ pendingDemand)
        nextRequirements records (.plain restDependencies dependencyScope) allowed outgoing ∧
      currentDemand = childDemand ++ restDemand ∧
      FocusDependencies dependencies childDependencies restDependencies ∧
      LexicalUnwind.UseTransition (.eval ⟨whole, runtimeScope, stack⟩)
        (.eval ⟨child, runtimeScope, .push (.plain plain) stack⟩) [] [] := by
  obtain ⟨nextInput, childDemand, restDemand, childReq, restReq, childDep, restDep,
    childSource, sourceContext, sameDemand, shape, path, evaluation⟩ := rich_focus_decompose current position
  obtain ⟨plain, contextSame, scopeSame, inputAnnotation, outputAnnotation⟩ :=
    RecursiveContexts.prepare_plain (DeclaredSources.expression_erase (expression_erase current))
      position scopeTyped nextInput.erase
  have frame : Frame operations policy contracts tables families world (.plain plain)
      nextInput input restDemand restReq (.plain restDep) allowed allowed :=
    .plain (by simpa only [contextSame, scopeSame] using sourceContext)
      (by simpa only [scopeSame] using scopeTyped) inputAnnotation outputAnnotation
  refine ⟨plain, nextInput, childDemand, restDemand, childReq, _, childDep, restDep,
    contextSame, scopeSame, childSource, .push (.ordinary frame) pending (List.Subset.refl _), sameDemand, shape, ?_⟩
  apply LexicalUnwind.UseTransition.evaluate
  · simpa only [scopeSame] using RawStep.focus plain (by simpa only [contextSame] using position) stack
  · cases position <;> first | assumption | trivial

/-- A returned value restores the source scope stored in the actual waiting
    frame. Latent annotations survive the value transport and context plug. -/
theorem lexical_plug_source
    (current : Expression operations policy contracts world allowed runtimeScope Environment.empty
      value input currentDemand currentRequirements dependencies)
    (pending : LexicalSegment operations policy contracts tables families actions world
      (.push (.plain plain) tail) input output pendingDemand pendingRequirements records dependencyScope allowed outgoing)
    (closed : ClosedValue value) :
    ∃ (nextInput : Value) (frameDemand tailDemand : List Nat),
    ∃ nextRequirements : Requirements frameDemand, ∃ tailRequirements : Requirements tailDemand,
    ∃ nextDependencies restDependencies restScope boundary,
      dependencyScope = .plain restDependencies restScope ∧
      currentDemand = [] ∧ pendingDemand = frameDemand ++ tailDemand ∧
      Expression operations policy contracts world boundary plain.scope Environment.empty
        (plain.context.plug value) nextInput frameDemand nextRequirements nextDependencies ∧
      LexicalSegment operations policy contracts tables families actions world
        tail nextInput output tailDemand tailRequirements records restScope boundary outgoing ∧
      FocusDependencies nextDependencies .pure restDependencies ∧
      LexicalUnwind.UseTransition (.eval ⟨value, runtimeScope, .push (.plain plain) tail⟩)
        (.eval ⟨plain.context.plug value, plain.scope, tail⟩) [] [] := by
  have empty := SourceTemplates.expression_value_demand
    (DeclaredSources.expression_erase (expression_erase current)) closed.1
  cases pending with
  | push frame rest bound => cases frame with
    | ordinary frame => cases frame with
      | plain context scope inputAnnotation outputAnnotation =>
          obtain ⟨combined, nextDependencies, source, shape, evaluation⟩ :=
            rich_context_plug context (Values.change_context (Values.summary current closed.1) closed.1 _ plain.scope)
          refine ⟨_, _, _, combined, _, nextDependencies, _, _, _, rfl, empty, rfl, source, rest, shape, ?_⟩
          apply LexicalUnwind.UseTransition.evaluate
          · exact .plug plain value closed runtimeScope tail
          · cases value <;> first | trivial | cases closed.1

#print axioms Ash.OneShot.SourceDependencyFrames.lexical_focus_source
#print axioms Ash.OneShot.SourceDependencyFrames.lexical_plug_source

#print axioms Ash.OneShot.SourceDependencyFrames.rich_focus_decompose
#print axioms Ash.OneShot.SourceDependencyFrames.pure_at_scope
#print axioms Ash.OneShot.SourceDependencyFrames.rich_context_plug
end Ash.OneShot.SourceDependencyFrames


namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations
open RecursiveRequirements (Requirements Store evaluate)
open OwnerPhaseTransitions (spendAll)

/-- Proof-only requirements for lexical abandonment. Each callback retains
    its actual enclosing stack; this is not an executable cleanup plan. -/
inductive UnwindTemplate (operations : Operations) (policy : Syntax.TicketPolicy)
    (contracts : Contracts) (tables : CallableProtectionFrames.Tables) (world : List Nat) :
    Stack → (demand : List Nat) → Requirements demand → Prop where
  | nil : UnwindTemplate operations policy contracts tables world .nil [] (.request [] [])
  | plain (tail : UnwindTemplate operations policy contracts tables world rest demand requirements) :
      UnwindTemplate operations policy contracts tables world (.push (.plain data) rest) demand requirements
  | handler (tail : UnwindTemplate operations policy contracts tables world rest demand requirements) :
      UnwindTemplate operations policy contracts tables world (.push (.handler data) rest) demand requirements
  | cell (tail : UnwindTemplate operations policy contracts tables world rest demand requirements) :
      UnwindTemplate operations policy contracts tables world (.push (.cell identity payload scope answer) rest) demand requirements
  | cleanup (callback : ValueSummary operations policy contracts world Environment.empty [] action.action
        (.function .unit .unit action.requests latent dependencies))
      (tail : UnwindTemplate operations policy contracts tables world rest demand requirements) :
      UnwindTemplate operations policy contracts tables world (.push (.armed action) rest) ([] ++ demand)
        (.sequence (.request (OwnerPhases.ofStack tables rest) (qualify true latent)) requirements)
  | live (saved : UnwindTemplate operations policy contracts tables world captured savedDemand savedRequirements)
      (tail : UnwindTemplate operations policy contracts tables world rest tailDemand tailRequirements) :
      UnwindTemplate operations policy contracts tables world (.live owner input answer captured caller rest)
        (savedDemand ++ ([owner] ++ tailDemand))
        (.sequence (savedRequirements.prepend (OwnerPhases.ofStack tables (.push (.retiring owner) rest)))
          (.sequence (.retire owner) tailRequirements))
  | spent (tail : UnwindTemplate operations policy contracts tables world rest demand requirements) :
      UnwindTemplate operations policy contracts tables world (.spent owner answer caller rest) ([] ++ demand)
        (.sequence (.spent owner) requirements)
  | retiring (tail : UnwindTemplate operations policy contracts tables world rest demand requirements) :
      UnwindTemplate operations policy contracts tables world (.push (.retiring owner) rest) ([owner] ++ demand)
        (.sequence (.retire owner) requirements)

/-- A summary accounts for each recursively owned continuation exactly once.
    Its order is saved scopes first, followed by their enclosing owner. -/
theorem UnwindTemplate.ownership
    (source : UnwindTemplate operations policy contracts tables world stack demand requirements) :
    demand.Perm (ownedTickets stack) := by
  induction source with
  | nil => exact .nil
  | plain tail ih | handler tail ih | cell tail ih | cleanup callback tail ih | spent tail ih => exact ih
  | retiring tail ih => exact .cons _ ih
  | @live captured savedDemand savedRequirements rest tailDemand tailRequirements owner input answer caller saved tail ihSaved ihTail =>
      apply (ihSaved.append (List.Perm.cons owner ihTail)).trans
      apply List.perm_iff_count.mpr
      intro item
      simp only [ownedTickets, List.count_append, List.count_cons]
      omega

/-- Retain the summary and its dependency scope in one structural derivation.
The cleanup rule uses one actual callback typing witness for both its effect
requirements and its dependency annotation. Abandoned normal code contributes
no execution requirement. -/
inductive UnwindSource (operations : Operations) (policy : Syntax.TicketPolicy)
    (contracts : Contracts) (tables : CallableProtectionFrames.Tables) (families : Families) (world : List Nat) :
    Stack → (demand : List Nat) → Requirements demand → DependencyScope → Prop where
  | nil : UnwindSource operations policy contracts tables families world .nil [] (.request [] []) .nil
  | plain (tail : UnwindSource operations policy contracts tables families world rest demand requirements restScope) :
      UnwindSource operations policy contracts tables families world (.push (.plain data) rest) demand requirements
        (.plain dependencies restScope)
  | handler (declaration : Frame operations policy contracts tables families world
        (.handler data) answer answer [] (.request [] [])
        (.handler data.effectInst (tables data) (families data)) (data.effectInst :: residual) residual)
      (tail : UnwindSource operations policy contracts tables families world rest demand requirements restScope) :
      UnwindSource operations policy contracts tables families world (.push (.handler data) rest) demand requirements
        (.handler data.effectInst (tables data) (families data) restScope)
  | cell (tail : UnwindSource operations policy contracts tables families world rest demand requirements restScope) :
      UnwindSource operations policy contracts tables families world (.push (.cell identity payload caller answer) rest) demand requirements
        (.cell identity restScope)
  | cleanup (callback : ValueSummary operations policy contracts world Environment.empty [] action.action
        (.function .unit .unit action.requests latent dependencies))
      (tail : UnwindSource operations policy contracts tables families world rest demand requirements restScope) :
      UnwindSource operations policy contracts tables families world (.push (.armed action) rest) ([] ++ demand)
        (.sequence (.request (OwnerPhases.ofStack tables rest) (qualify true latent)) requirements)
        (.cleanup action.requests dependencies restScope)
  | live (saved : UnwindSource operations policy contracts tables families world captured savedDemand savedRequirements savedScope)
      (tail : UnwindSource operations policy contracts tables families world rest tailDemand tailRequirements restScope) :
      UnwindSource operations policy contracts tables families world (.live owner input answer captured caller rest)
        (savedDemand ++ ([owner] ++ tailDemand))
        (.sequence (savedRequirements.prepend (OwnerPhases.ofStack tables (.push (.retiring owner) rest)))
          (.sequence (.retire owner) tailRequirements)) (.live owner savedScope restScope)
  | spent (tail : UnwindSource operations policy contracts tables families world rest demand requirements restScope) :
      UnwindSource operations policy contracts tables families world (.spent owner answer caller rest) ([] ++ demand)
        (.sequence (.spent owner) requirements) (.spent owner restScope)
  | retiring (tail : UnwindSource operations policy contracts tables families world rest demand requirements restScope) :
      UnwindSource operations policy contracts tables families world (.push (.retiring owner) rest) ([owner] ++ demand)
        (.sequence (.retire owner) requirements) (.running restScope)

theorem UnwindSource.template
    (source : UnwindSource operations policy contracts tables families world stack demand requirements dependencyScope) :
    UnwindTemplate operations policy contracts tables world stack demand requirements := by
  induction source with
  | nil => exact .nil
  | plain tail ih => exact .plain ih
  | handler declaration tail ih => exact .handler ih
  | cell tail ih => exact .cell ih
  | cleanup callback tail ih => exact .cleanup callback ih
  | live saved tail ihSaved ihTail => exact .live ihSaved ihTail
  | spent tail ih => exact .spent ih
  | retiring tail ih => exact .retiring ih

theorem UnwindSource.realizes
    (source : UnwindSource operations policy contracts tables families world stack demand requirements dependencyScope) :
    SourceDependencyCapture.Realizes tables families dependencyScope stack := by
  induction source with
  | nil => exact .nil
  | plain tail ih => exact .push .plain ih
  | handler declaration tail ih => exact .push .handler ih
  | cell tail ih => exact .push .cell ih
  | cleanup callback tail ih => exact .push .cleanup ih
  | live saved tail ihSaved ihTail => exact .live ihSaved ihTail
  | spent tail ih => exact .spent ih
  | retiring tail ih => exact .push .retiring ih

/-- An unprotected rich source capture supplies the lexical summary directly.
    Running callbacks and completion markers cannot enter this construction. -/
theorem LexicalSegment.unwind_source
    (source : LexicalSegment operations policy contracts tables families actions world
      stack input output demand requirements records dependencyScope incoming outgoing)
    (unprotected : ProtectionContexts.protectedMode stack.erase = false) :
    ∃ closingDemand, ∃ closingRequirements : Requirements closingDemand,
      UnwindSource operations policy contracts tables families world stack closingDemand closingRequirements dependencyScope := by
  induction source with
  | nil => exact ⟨[], _, .nil⟩
  | push frame tail bound ih => cases frame with
    | ordinary frame => cases frame with
      | plain context scope inputAnnotation outputAnnotation =>
          obtain ⟨demand, requirements, rest⟩ := ih unprotected
          exact ⟨_, _, .plain rest⟩
      | handler scope annotation clauses coverage unique declarations capabilities modes =>
          obtain ⟨demand, requirements, rest⟩ := ih unprotected
          exact ⟨_, _, .handler (.handler scope annotation clauses coverage unique declarations capabilities modes) rest⟩
      | cell scope noEscape annotation interface =>
          obtain ⟨demand, requirements, rest⟩ := ih unprotected
          exact ⟨_, _, .cell rest⟩
      | armed scope callback annotation interface =>
          obtain ⟨demand, requirements, rest⟩ := ih unprotected
          exact ⟨_, _, .cleanup callback rest⟩
      | running | closing | retiring => cases unprotected
    | unwinding | closing | retiring => cases unprotected
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      obtain ⟨savedUnprotected, tailUnprotected⟩ := Bool.or_eq_false_iff.mp unprotected
      obtain ⟨savedDemand, savedRequirements, inside⟩ := ihSaved savedUnprotected
      obtain ⟨tailDemand, tailRequirements, rest⟩ := ihTail tailUnprotected
      exact ⟨_, _, .live inside rest⟩
  | spent known annotation scope tail bound ih =>
      obtain ⟨demand, requirements, rest⟩ := ih unprotected
      exact ⟨_, _, .spent rest⟩

#print axioms Ash.OneShot.SourceDependencyFrames.UnwindSource.template
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindSource.realizes
#print axioms Ash.OneShot.SourceDependencyFrames.LexicalSegment.unwind_source

/-- The existing summary projection is obtained from the same authenticated
source derivation; its public interface is unchanged. -/
theorem LexicalSegment.unwind_template
    (source : LexicalSegment operations policy contracts tables families actions world
      stack input output demand requirements records dependencyScope incoming outgoing)
    (unprotected : ProtectionContexts.protectedMode stack.erase = false) :
    ∃ closingDemand, ∃ closingRequirements : Requirements closingDemand,
      UnwindTemplate operations policy contracts tables world stack closingDemand closingRequirements := by
  obtain ⟨closingDemand, closingRequirements, checked⟩ := source.unwind_source unprotected
  exact ⟨closingDemand, closingRequirements, checked.template⟩

#print axioms Ash.OneShot.SourceDependencyFrames.UnwindTemplate.ownership
#print axioms Ash.OneShot.SourceDependencyFrames.LexicalSegment.unwind_template

theorem evaluate_request_at : evaluate store receiving before (.request nearer raw) =
    OwnerSource.exportAt (nearer ++ receiving) before raw := by
  simpa only [Requirements.prepend, List.nil_append] using
    (RecursiveRequirements.evaluate_prepend (store := store) (receiving := receiving)
      (before := before) (prefixContext := nearer) (.request [] raw)).trans RecursiveContexts.evaluate_request

private theorem unwind_template_reindex
    (source : UnwindTemplate operations policy contracts tables world stack demand requirements)
    (same : demand = nextDemand) :
    ∃ next : Requirements nextDemand,
      UnwindTemplate operations policy contracts tables world stack nextDemand next ∧
      ∀ store receiving before, evaluate store receiving before next = evaluate store receiving before requirements := by
  cases same
  exact ⟨requirements, source, fun _ _ _ => rfl⟩

/-- Enclosing-stack composition retains the interpretation suffix of every
    callback, including callbacks inside dormant captures. -/
theorem UnwindTemplate.append
    (first : UnwindTemplate operations policy contracts tables world front a firstRequirements)
    (second : UnwindTemplate operations policy contracts tables world tail b secondRequirements) :
    ∃ combined : Requirements (a ++ b),
      UnwindTemplate operations policy contracts tables world (front.append tail) (a ++ b) combined ∧
      ∀ store receiving before, evaluate store receiving before combined =
        merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) before firstRequirements)
          (evaluate store receiving (spendAll before a) secondRequirements) := by
  induction first with
  | nil =>
      exact ⟨_, second, by intros; simp only [RecursiveRecomposition.evaluate_empty, spendAll,
        RecursiveRecomposition.merge_empty_left]⟩
  | plain next ih =>
      obtain ⟨combined, result, evaluation⟩ := ih
      exact ⟨_, .plain result, evaluation⟩
  | handler next ih =>
      obtain ⟨combined, result, evaluation⟩ := ih
      exact ⟨_, .handler result, evaluation⟩
  | cell next ih =>
      obtain ⟨combined, result, evaluation⟩ := ih
      exact ⟨_, .cell result, evaluation⟩
  | cleanup callback next ih =>
      obtain ⟨combined, result, evaluation⟩ := ih
      refine ⟨_, .cleanup callback result, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, evaluate_request_at,
        OwnerPhases.stack_append, List.append_assoc, evaluation, spendAll, List.nil_append, merge_assoc]
  | spent next ih =>
      obtain ⟨combined, result, evaluation⟩ := ih
      refine ⟨_, .spent result, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_spent,
        evaluation, spendAll, List.nil_append, merge_assoc]
  | retiring next ih =>
      obtain ⟨combined, result, evaluation⟩ := ih
      refine ⟨_, .retiring result, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveClosing.evaluate_retire,
        evaluation, spendAll, List.nil_append, List.cons_append, merge_assoc]
  | @live captured savedDemand savedRequirements rest tailDemand tailRequirements owner input answer caller saved next ihSaved ihNext =>
      obtain ⟨combined, result, evaluation⟩ := ihNext
      obtain ⟨joined, rebuilt, reindexed⟩ := unwind_template_reindex
        (UnwindTemplate.live (owner := owner) (input := input) (answer := answer) (caller := caller) saved result)
        (nextDemand := (savedDemand ++ ([owner] ++ tailDemand)) ++ b) (by simp only [List.append_assoc])
      refine ⟨joined, rebuilt, ?_⟩
      intro store receiving before
      rw [reindexed]
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        RecursiveClosing.evaluate_retire, OwnerPhases.ofStack, OwnerPhases.stack_append,
        List.cons_append, List.append_assoc, evaluation, PhaseRechecking.spendAll_append, spendAll, merge_assoc]

/-- Closing requirements contain direct callback effects and retirements;
    evaluating them does not consult a continuation-template store. -/
theorem UnwindTemplate.store
    (source : UnwindTemplate operations policy contracts tables world stack demand requirements) :
    evaluate first receiving before requirements = evaluate second receiving before requirements := by
  induction source generalizing receiving before with
  | nil => simp only [RecursiveRecomposition.evaluate_empty]
  | plain next ih | handler next ih | cell next ih => exact ih
  | cleanup callback next ih =>
      simp only [RecursiveRequirements.evaluate_sequence, evaluate_request_at, ih]
  | spent next ih =>
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_spent, ih]
  | retiring next ih =>
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveClosing.evaluate_retire, ih]
  | live saved next ihSaved ihNext =>
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        RecursiveClosing.evaluate_retire, ihSaved, ihNext]

/-- Fresh continuation allocation preserves the same source-derived closing
    record. No callback or lexical interpretation is replaced. -/
theorem UnwindTemplate.transport
    (source : UnwindTemplate operations policy contracts tables world stack demand requirements)
    (extension : contracts.Extends nextContracts) (larger : world ⊆ nextWorld) :
    UnwindTemplate operations policy nextContracts tables nextWorld stack demand requirements := by
  induction source with
  | nil => exact .nil
  | plain next ih => exact .plain ih
  | handler next ih => exact .handler ih
  | cell next ih => exact .cell ih
  | cleanup callback next ih => exact .cleanup (expression_transport callback extension larger) ih
  | live saved next ihSaved ihNext => exact .live ihSaved ihNext
  | spent next ih => exact .spent ih
  | retiring next ih => exact .retiring ih

#print axioms Ash.OneShot.SourceDependencyFrames.UnwindTemplate.append
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindTemplate.store
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindTemplate.transport

/-- Each administrative unwind step preserves the checked effect row while
    spending exactly the continuation owners discharged by that runtime step. -/
theorem UnwindTemplate.advance_checked
    (source : UnwindTemplate operations policy contracts tables world stack demand requirements)
    (step : LexicalUnwind.Advance stack after discharged)
    (checked : RecursiveRequirements.Checked entries receiving before requirements row) :
    ∃ nextDemand, ∃ nextRequirements : Requirements nextDemand,
      UnwindTemplate operations policy contracts tables world after nextDemand nextRequirements ∧
      RecursiveRequirements.Checked entries receiving
        (spendAll before (discharged.filterMap Syntax.ticketProjection)) nextRequirements row := by
  cases step with
  | plain => cases source with | plain tail => exact ⟨_, _, tail, checked⟩
  | handler => cases source with | handler tail => exact ⟨_, _, tail, checked⟩
  | cell => cases source with | cell tail => exact ⟨_, _, tail, checked⟩
  | spent => cases source with
    | spent tail =>
      obtain ⟨firstRow, secondRow, first, second, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
      have firstEmpty : firstRow = [] := by
        have evaluated := RecursiveRequirements.checked_complete first
        rw [RecursiveRecomposition.evaluate_spent] at evaluated
        split at evaluated
        · exact (Option.some.inj evaluated).symm
        · cases evaluated
      subst firstRow
      exact ⟨_, _, tail, second⟩
  | retire => cases source with
    | retiring tail =>
      obtain ⟨firstRow, secondRow, first, second, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
      have firstEmpty : firstRow = [] := by
        have evaluated := RecursiveRequirements.checked_complete first
        rw [RecursiveClosing.evaluate_retire] at evaluated
        split at evaluated
        · exact (Option.some.inj evaluated).symm
        · cases evaluated
      subst firstRow
      exact ⟨_, _, tail, second⟩
  | live => cases source with
    | live saved tail =>
      obtain ⟨combined, result, evaluation⟩ := saved.append (UnwindTemplate.retiring tail)
      refine ⟨_, combined, result, RecursiveRequirements.evaluate_sound ?_⟩
      rw [evaluation]
      simpa only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        List.filterMap_nil, spendAll] using RecursiveRequirements.checked_complete checked

#print axioms Ash.OneShot.SourceDependencyFrames.UnwindTemplate.advance_checked

/-- The summary's leading cleanup row is exactly the row checked for the
    real callback application under the actual unwinding marker. -/
theorem UnwindTemplate.start_cleanup
    (source : UnwindTemplate operations policy contracts tables world
      (.push (.armed action) rest) demand requirements)
    (checked : RecursiveRequirements.Checked entries receiving before requirements row) :
    ∃ latent dependencies callbackRow tailRow, ∃ tailRequirements : Requirements demand,
      Expression operations policy contracts world action.requests .none Environment.empty
        (.app action.action .unit) .unit []
        (.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent)
        (.sequence .pure (.sequence .pure dependencies)) ∧
      UnwindTemplate operations policy contracts tables world rest demand tailRequirements ∧
      RecursiveRequirements.Checked entries
        (OwnerPhases.ofStack tables (.push (.unwinding action) rest) ++ receiving) before
        (.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent) callbackRow ∧
      RecursiveRequirements.Checked entries receiving before tailRequirements tailRow ∧
      row = callbackRow ++ tailRow := by
  cases source with
  | @cleanup latent dependencies rest demand requirements action callback tail =>
      obtain ⟨callbackRow, tailRow, callbackCheck, tailCheck, same⟩ :=
        RecursiveRequirements.checked_sequence_parts checked
      have exported := RecursiveRequirements.checked_complete callbackCheck
      rw [evaluate_request_at] at exported
      have actual : OwnerSource.exportAt
          (OwnerPhases.ofStack tables (.push (.unwinding action) rest) ++ receiving) before latent = some callbackRow := by
        simpa only [OwnerPhases.ofStack, OwnerPhases.frameEntry, ExecFrame.erase, ActionData.erase,
          ProtectionContexts.frameProtected, OwnerPhaseTransitions.project, OwnerSource.exportAt,
          residualize, DisposalProtection.through_barrier, List.cons_append] using exported
      have pureCheck : RecursiveRequirements.Checked entries
          (OwnerPhases.ofStack tables (.push (.unwinding action) rest) ++ receiving) before (.request [] []) [] :=
        .request (by simp [OwnerSource.exportAt, residual_empty])
      refine ⟨_, _, callbackRow, tailRow, _,
        .app (Values.change_context callback action.closed.1 action.requests .none) .unit (List.Subset.refl _),
        tail, ?_, tailCheck, same⟩
      exact .emitAfter (.sequence pureCheck pureCheck) actual

#print axioms Ash.OneShot.SourceDependencyFrames.evaluate_request_at
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindTemplate.start_cleanup
end Ash.OneShot.SourceDependencyFrames


namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations
open RecursiveRequirements (Requirements Store Key)

/-- Disposal records retain actual lexical captures. Protected captures have
    no disposal entry; their nested records are still retained. -/
inductive UnwindRecords (operations : Operations) (policy : Syntax.TicketPolicy)
    (contracts : Contracts) (tables : CallableProtectionFrames.Tables) (world : List Nat) :
    Stack → Store → Prop where
  | nil : UnwindRecords operations policy contracts tables world .nil []
  | push (tail : UnwindRecords operations policy contracts tables world rest records) :
      UnwindRecords operations policy contracts tables world (.push frame rest) records
  | blocked (held : ProtectionContexts.protectedMode capture.erase = true)
      (saved : UnwindRecords operations policy contracts tables world capture nested)
      (tail : UnwindRecords operations policy contracts tables world rest remaining) :
      UnwindRecords operations policy contracts tables world (.live owner input answer capture caller rest) (nested ++ remaining)
  | close (unprotected : ProtectionContexts.protectedMode capture.erase = false)
      (summary : UnwindTemplate operations policy contracts tables world capture demand requirements)
      (saved : UnwindRecords operations policy contracts tables world capture nested)
      (tail : UnwindRecords operations policy contracts tables world rest remaining) :
      UnwindRecords operations policy contracts tables world (.live owner input answer capture caller rest)
        ((⟨owner, .dispose⟩, ⟨demand, requirements⟩) :: (nested ++ remaining))
  | spent (tail : UnwindRecords operations policy contracts tables world rest records) :
      UnwindRecords operations policy contracts tables world (.spent owner answer caller rest) records

/-- Collection needs only present rich source evidence; no execution, plan,
    successful row check or future invariant is a premise. -/
theorem LexicalSegment.unwind_records
    (source : LexicalSegment operations policy contracts tables families actions world
      stack input output demand requirements records dependencyScope incoming outgoing) :
    ∃ disposals, UnwindRecords operations policy contracts tables world stack disposals := by
  induction source with
  | nil bound => exact ⟨[], .nil⟩
  | push head tail bound ih =>
      obtain ⟨records, collected⟩ := ih
      exact ⟨_, .push collected⟩
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      obtain ⟨nested, captured⟩ := ihSaved
      obtain ⟨remaining, rest⟩ := ihTail
      cases protection : ProtectionContexts.protectedMode _ with
      | true => exact ⟨_, .blocked protection captured rest⟩
      | false =>
          obtain ⟨closingDemand, closingRequirements, summary⟩ := saved.unwind_template protection
          exact ⟨_, .close protection summary captured rest⟩
  | spent known annotation scope tail bound ih =>
      obtain ⟨records, collected⟩ := ih
      exact ⟨_, .spent collected⟩

inductive UnwindCertified (operations : Operations) (policy : Syntax.TicketPolicy)
    (contracts : Contracts) (tables : CallableProtectionFrames.Tables) (world : List Nat)
    (root : Stack) : Key → RecursiveRequirements.Template → Prop where
  | dispose (located : SourceTemplates.CapturedIn owner capture root)
      (unprotected : ProtectionContexts.protectedMode capture.erase = false)
      (summary : UnwindTemplate operations policy contracts tables world capture demand requirements) :
      UnwindCertified operations policy contracts tables world root ⟨owner, .dispose⟩ ⟨demand, requirements⟩

theorem UnwindCertified.transport
    (source : UnwindCertified operations policy contracts tables world first key body)
    (move : ∀ owner capture, SourceTemplates.CapturedIn owner capture first → SourceTemplates.CapturedIn owner capture second) :
    UnwindCertified operations policy contracts tables world second key body := by
  cases source with
  | dispose located unprotected summary => exact .dispose (move _ _ located) unprotected summary

/-- Membership authenticates both the key and the exact saved lexical stack. -/
theorem UnwindRecords.certified
    (source : UnwindRecords operations policy contracts tables world stack records)
    (member : (key, body) ∈ records) :
    UnwindCertified operations policy contracts tables world stack key body := by
  induction source with
  | nil => cases member
  | push tail ih => exact (ih member).transport (fun _ _ located => .push located)
  | blocked held saved tail ihSaved ihTail =>
      rcases List.mem_append.mp member with nested | remaining
      · exact (ihSaved nested).transport (fun _ _ located => .saved located)
      · exact (ihTail remaining).transport (fun _ _ located => .tail located)
  | close unprotected summary saved tail ihSaved ihTail =>
      rcases List.mem_cons.mp member with same | later
      · cases same; exact .dispose .here unprotected summary
      · rcases List.mem_append.mp later with nested | remaining
        · exact (ihSaved nested).transport (fun _ _ located => .saved located)
        · exact (ihTail remaining).transport (fun _ _ located => .tail located)
  | spent tail ih => exact (ih member).transport (fun _ _ located => .spent located)

theorem UnwindRecords.owners_sublist
    (source : UnwindRecords operations policy contracts tables world stack records) :
    (RecursiveTransport.recordOwners records).Sublist (ownedTickets stack) := by
  induction source with
  | nil => exact .slnil
  | push tail ih => rename_i frame; cases frame <;> first | exact ih | exact .cons _ ih
  | blocked held saved tail ihSaved ihTail =>
      simpa only [RecursiveTransport.recordOwners, List.map_append, ownedTickets] using List.Sublist.cons _ (ihSaved.append ihTail)
  | close unprotected summary saved tail ihSaved ihTail =>
      simpa only [RecursiveTransport.recordOwners, List.map_cons, List.map_append, ownedTickets] using
        List.Sublist.cons_cons _ (ihSaved.append ihTail)
  | spent tail ih => exact ih

theorem UnwindRecords.keys_unique
    (source : UnwindRecords operations policy contracts tables world stack records)
    (unique : (ownedTickets stack).Nodup) :
    (RecursiveTransport.recordKeys records).Nodup :=
  RecursiveTransport.record_keys_unique (source.owners_sublist.nodup unique)

theorem UnwindRecords.record_mode
    (source : UnwindRecords operations policy contracts tables world stack records)
    (member : (key, body) ∈ records) : key.mode = .dispose := by
  cases source.certified member
  rfl

/-- A lookup cannot invent a disposal budget: its demand is exactly the
    ownership of the captured stack named by that key. -/
theorem UnwindRecords.lookup_ownership
    (source : UnwindRecords operations policy contracts tables world stack records)
    (found : RecursiveRequirements.lookup key records = some ⟨demand, requirements⟩) :
    ∃ capture, SourceTemplates.CapturedIn key.owner capture stack ∧ key.mode = .dispose ∧
      ProtectionContexts.protectedMode capture.erase = false ∧
      UnwindTemplate operations policy contracts tables world capture demand requirements ∧
      demand.Perm (ownedTickets capture) := by
  cases source.certified (SourceTemplates.lookup_member found) with
  | dispose located unprotected summary => exact ⟨_, located, rfl, unprotected, summary, summary.ownership⟩

/-- Existing records survive extension of the source registry and resource
    history with their exact requirements unchanged. -/
theorem UnwindRecords.transport
    (source : UnwindRecords operations policy contracts tables world stack records)
    (extension : contracts.Extends nextContracts) (larger : world ⊆ nextWorld) :
    UnwindRecords operations policy nextContracts tables nextWorld stack records := by
  induction source with
  | nil => exact .nil
  | push tail ih => exact .push ih
  | blocked held saved tail ihSaved ihTail => exact .blocked held ihSaved ihTail
  | close unprotected summary saved tail ihSaved ihTail =>
      exact .close unprotected (summary.transport extension larger) ihSaved ihTail
  | spent tail ih => exact .spent ih

/-- Stack recomposition concatenates the same authenticated disposal entries. -/
theorem UnwindRecords.append
    (first : UnwindRecords operations policy contracts tables world front a)
    (second : UnwindRecords operations policy contracts tables world tail b) :
    UnwindRecords operations policy contracts tables world (front.append tail) (a ++ b) := by
  induction first with
  | nil => exact second
  | push rest ih => exact .push ih
  | blocked held saved rest ihSaved ihRest =>
      simpa only [Stack.append, List.append_assoc] using UnwindRecords.blocked held saved ihRest
  | close unprotected summary saved rest ihSaved ihRest =>
      simpa only [Stack.append, List.cons_append, List.append_assoc] using UnwindRecords.close unprotected summary saved ihRest
  | spent rest ih => exact .spent ih

theorem LexicalSegment.record_owners_sublist
    (source : LexicalSegment operations policy contracts tables families actions world
      stack input output demand requirements records dependencyScope incoming outgoing) :
    (RecursiveTransport.recordOwners records).Sublist (ownedTickets stack) := by
  induction source with
  | nil => exact .slnil
  | @push entry input middle headDemand first layer inner outer rest output tailDemand second records restScope outgoing incoming head tail bound ih =>
      cases entry <;> first | exact ih | exact .cons _ ih
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      simpa only [RecursiveTransport.recordOwners, List.map_cons, List.map_append, ownedTickets] using
        List.Sublist.cons_cons _ (ihSaved.append ihTail)
  | spent known annotation scope tail bound ih => exact ih

theorem LexicalSegment.record_mode
    (source : LexicalSegment operations policy contracts tables families actions world
      stack input output demand requirements records dependencyScope incoming outgoing)
    (member : (key, body) ∈ records) : key.mode = .resume := by
  induction source with
  | nil => cases member
  | push head tail bound ih => exact ih member
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      rcases List.mem_cons.mp member with same | later
      · cases same; rfl
      · rcases List.mem_append.mp later with nested | remaining
        · exact ihSaved nested
        · exact ihTail remaining
  | spent known annotation scope tail bound ih => exact ih member

/-- Resume and disposal share owner identities, but their mode-tagged keys
    remain unique. Reuse the existing record-key and list laws. -/
theorem LexicalSegment.combined_unwind_keys_unique
    (source : LexicalSegment operations policy contracts tables families actions world
      stack input output demand requirements resumes dependencyScope incoming outgoing)
    (closing : UnwindRecords operations policy contracts tables world stack disposals)
    (unique : (ownedTickets stack).Nodup) :
    (RecursiveTransport.recordKeys (resumes ++ disposals)).Nodup := by
  have first := RecursiveTransport.record_keys_unique (source.record_owners_sublist.nodup unique)
  have second := closing.keys_unique unique
  simp only [RecursiveTransport.recordKeys, List.map_append]
  refine List.nodup_append.mpr ⟨first, second, ?_⟩
  intro key left other right same
  obtain ⟨⟨leftKey, leftBody⟩, leftMember, leftSame⟩ := List.mem_map.mp left
  obtain ⟨⟨rightKey, rightBody⟩, rightMember, rightSame⟩ := List.mem_map.mp right
  have modes := congrArg Key.mode (leftSame.trans (same.trans rightSame.symm))
  rw [source.record_mode leftMember, closing.record_mode rightMember] at modes
  cases modes

#print axioms Ash.OneShot.SourceDependencyFrames.UnwindRecords.append
#print axioms Ash.OneShot.SourceDependencyFrames.LexicalSegment.record_owners_sublist
#print axioms Ash.OneShot.SourceDependencyFrames.LexicalSegment.record_mode
#print axioms Ash.OneShot.SourceDependencyFrames.LexicalSegment.combined_unwind_keys_unique

#print axioms Ash.OneShot.SourceDependencyFrames.LexicalSegment.unwind_records
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindCertified.transport
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindRecords.certified
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindRecords.owners_sublist
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindRecords.keys_unique
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindRecords.record_mode
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindRecords.lookup_ownership
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindRecords.transport
namespace UnwindExamples
open InitialCleanupRouteGap
open ProtectionResiduals

def richOperations : SourceDependencyAnnotations.Operations := fun _ _ => some (.unit, .unit)
def richContracts : SourceDependencyAnnotations.Contracts := fun _ => none
def tables : CallableProtectionFrames.Tables := fun handler =>
  if handler.activation = 100 then discardTable else resumeTable

theorem callback_source :
    ValueSummary richOperations policy richContracts [] Environment.empty [] action.action
      (.function .unit .unit action.requests [⟨inner, 0, false⟩] (.sequence .pure (.request inner 0))) := by
  apply Expression.lambda
  · exact .perform rfl (by simp [action]) .unit (by simp [ScopedPorts.InWorld, Value.erase, CoherentSourceTypes.Value.port, ScopedPorts.Port.resources])
  · exact .emitAfter (layers := []) (.request (layers := []))
  · simp [ScopedPorts.InWorld, CoherentSourceTypes.Value.port, ScopedPorts.Port.resources,
      Value.erase, action, inner, Instance.resources]
  · intro request member
    have same := List.mem_singleton.mp member
    subst request
    exact List.mem_cons_self

def closingRequirements : Requirements [] :=
  .sequence (.request (OwnerPhases.ofStack tables innerStack) [⟨inner, 0, true⟩]) (.request [] [])

/-- The existing planner-gap callback retains the two actual handler scopes. -/
theorem retained_handler_summary :
    UnwindTemplate richOperations policy richContracts tables [] capture [] closingRequirements :=
  .cleanup callback_source (.handler (.handler .nil))

theorem retained_handler_checked :
    RecursiveRequirements.Checked [] [] OwnerPhaseTransitions.empty closingRequirements [] := by
  apply RecursiveRequirements.evaluate_sound
  simp only [closingRequirements, RecursiveRequirements.evaluate, RecursiveRequirements.evaluateFuel]
  decide

/-- Removing the callback's lexical handler leaves an outward requirement;
    the same callback cannot be certified as a closed disposal. -/
theorem dropped_handler_not_closed :
    ¬ RecursiveRequirements.Checked [] [] OwnerPhaseTransitions.empty
      (.sequence (.request [] [⟨inner, 0, true⟩]) (.request [] [])) [] := by
  intro checked
  have evaluated := RecursiveRequirements.checked_complete checked
  simp only [RecursiveRequirements.evaluate_sequence, evaluate_request_at, OwnerSource.exportAt,
    OwnerPhaseTransitions.project, residualize, merge, List.nil_append] at evaluated
  cases evaluated

/-- Collection authenticates this actual saved capture without makePlan. -/
theorem retained_handler_record :
    UnwindRecords richOperations policy richContracts tables []
      (.live 103 .unit .unit capture .none .nil)
      [(⟨103, .dispose⟩, ⟨[], closingRequirements⟩)] :=
  .close rfl retained_handler_summary (.push (.push (.push .nil))) .nil

end UnwindExamples
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindExamples.callback_source
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindExamples.retained_handler_summary
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindExamples.retained_handler_checked
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindExamples.dropped_handler_not_closed
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindExamples.retained_handler_record
end Ash.OneShot.SourceDependencyFrames


namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations
open RecursiveRequirements (Requirements Store)

/-- Every physically owned continuation has a source contract, including
    owners awaiting retirement behind lexical cleanup. -/
theorem LexicalSegment.owned_registered
    (source : LexicalSegment operations policy contracts tables families actions world
      stack input output demand requirements records dependencyScope incoming outgoing)
    (member : owner ∈ ownedTickets stack) : ∃ contract, contracts owner = some contract := by
  induction source with
  | nil => cases member
  | push head tail bound ih => cases head with
    | ordinary head => cases head with
      | plain | handler | cell | armed | running | closing => exact ih member
      | retiring known interface =>
          rcases List.mem_cons.mp member with same | later
          · subst owner; exact ⟨_, known⟩
          · exact ih later
    | unwinding | closing => exact ih member
    | retiring known =>
        rcases List.mem_cons.mp member with same | later
        · subst owner; exact ⟨_, known⟩
        · exact ih later
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      rcases List.mem_cons.mp member with same | later
      · subst owner; exact ⟨_, known⟩
      · rcases List.mem_append.mp later with inside | outside
        · exact ihSaved inside
        · exact ihTail outside
  | spent known annotation scope tail bound ih => exact ih member

theorem LexicalSegment.fresh_unowned
    (source : LexicalSegment operations policy contracts tables families actions world
      stack input output demand requirements records dependencyScope incoming outgoing)
    (fresh : contracts owner = none) : owner ∉ ownedTickets stack := by
  intro member
  obtain ⟨contract, known⟩ := source.owned_registered member
  rw [fresh] at known
  cases known

theorem LexicalSegment.capture_unique
    (source : LexicalSegment operations policy contracts tables families actions world
      whole input output demand requirements records dependencyScope incoming outgoing)
    (cut : HandlerCut requested whole capture tail handler)
    (unique : (ownedTickets whole).Nodup) (fresh : contracts owner = none) :
    (ownedTickets (.live owner inputType handler.answer capture handler.scope tail)).Nodup := by
  rw [RecursiveCapture.capture_owned cut]
  exact List.nodup_cons.mpr ⟨source.fresh_unowned fresh, unique⟩

/-- Split the existing entries at the actual lexical stack boundary. The
    proof follows RecursiveRecords.split_append with lexical summaries. -/
theorem UnwindRecords.split_append
    (source : UnwindRecords operations policy contracts tables world (front.append tail) records) :
    ∃ a b, UnwindRecords operations policy contracts tables world front a ∧
      UnwindRecords operations policy contracts tables world tail b ∧ records = a ++ b := by
  induction front generalizing records with
  | nil => exact ⟨[], records, .nil, source, rfl⟩
  | push frame front ih => cases source with
      | push rest =>
          obtain ⟨a, b, first, second, same⟩ := ih rest
          exact ⟨a, b, .push first, second, same⟩
  | live owner input answer saved caller front ihSaved ihFront => cases source with
      | blocked held nested rest =>
          obtain ⟨a, b, first, second, same⟩ := ihFront rest
          exact ⟨_, b, .blocked held nested first, second, by simp only [same, List.append_assoc]⟩
      | close unprotected summary nested rest =>
          obtain ⟨a, b, first, second, same⟩ := ihFront rest
          exact ⟨_, b, .close unprotected summary nested first, second, by simp only [same, List.cons_append, List.append_assoc]⟩
  | spent owner answer caller front ih => cases source with
      | spent rest =>
          obtain ⟨a, b, first, second, same⟩ := ih rest
          exact ⟨a, b, .spent first, second, same⟩

theorem UnwindRecords.capture_with_template
    (closing : UnwindRecords operations policy contracts tables world whole records)
    (cut : HandlerCut requested whole capture tail handler)
    (unprotected : ProtectionContexts.protectedMode capture.erase = false)
    (summary : UnwindTemplate operations policy contracts tables world capture demand requirements) :
    UnwindRecords operations policy contracts tables world
      (.live owner input answer capture caller tail)
      ((⟨owner, .dispose⟩, ⟨demand, requirements⟩) :: records) := by
  obtain ⟨a, b, first, second, same⟩ := UnwindRecords.split_append (handler_cut_reconstructs cut ▸ closing)
  rw [same]
  exact .close unprotected summary first second

/-- Capturing a running cleanup preserves nested records without providing
    a disposal entry for the protected new continuation. -/
theorem UnwindRecords.capture_protected
    (closing : UnwindRecords operations policy contracts tables world whole records)
    (cut : HandlerCut requested whole capture tail handler)
    (held : ProtectionContexts.protectedMode capture.erase = true) :
    UnwindRecords operations policy contracts tables world
      (.live owner input answer capture caller tail) records := by
  obtain ⟨a, b, first, second, same⟩ := UnwindRecords.split_append (handler_cut_reconstructs cut ▸ closing)
  rw [same]
  exact .blocked held first second

#print axioms Ash.OneShot.SourceDependencyFrames.LexicalSegment.owned_registered
#print axioms Ash.OneShot.SourceDependencyFrames.LexicalSegment.fresh_unowned
#print axioms Ash.OneShot.SourceDependencyFrames.LexicalSegment.capture_unique
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindRecords.split_append
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindRecords.capture_with_template
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindRecords.capture_protected

theorem LexicalFrame.row_source
    (source : LexicalFrame operations policy contracts tables families world
      frame input output demand requirements layer incoming outgoing) :
    ClauseRowAdmission.StoreFrame operations.erase policy contracts.erase world
      frame input.erase output.erase demand requirements := by
  cases source with
  | ordinary frame => exact .ordinary (DeclaredSourceFrames.frame_erase frame.erase.source)
  | unwinding scope callback annotation interface => exact .unwinding scope (DeclaredSourceValues.erase (value_erase callback)) annotation
  | closing scope => exact .closing (ScopedPorts.effect_scope_known_has_types scope)
  | retiring known => exact .retiring (contract_erase_known known)

theorem LexicalSegment.row_source
    (source : LexicalSegment operations policy contracts tables families actions world
      stack input output demand requirements records dependencyScope incoming outgoing) :
    ClauseRowAdmission.StoreSegment operations.erase policy contracts.erase tables world
      stack input.erase output.erase demand requirements records := by
  induction source with
  | nil => exact .nil
  | push head tail bound ih => exact .push head.row_source ih
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live (contract_erase_known known) inputAnnotation answerAnnotation
        (ScopedPorts.effect_scope_known_has_types scope) held ihSaved ihTail
  | spent known annotation scope tail bound ih =>
      exact .spent (contract_erase_known known) annotation (ScopedPorts.effect_scope_known_has_types scope) ih

theorem UnwindTemplate.row_source
    (source : UnwindTemplate operations policy contracts tables world stack demand requirements) :
    ClauseRowAdmission.StoreClosingTemplate operations.erase policy contracts.erase tables world stack demand requirements := by
  induction source with
  | nil => exact .nil
  | plain tail ih => exact .plain ih
  | handler tail ih => exact .handler ih
  | cell tail ih => exact .cell ih
  | cleanup callback tail ih => exact .cleanup (DeclaredSourceValues.erase (value_erase callback)) ih
  | live saved tail ihSaved ihTail => exact .live ihSaved ihTail
  | spent tail ih => exact .spent ih
  | retiring tail ih => exact .retiring ih

theorem UnwindRecords.row_source
    (source : UnwindRecords operations policy contracts tables world stack records) :
    ClauseRowAdmission.StoreClosingRecords operations.erase policy contracts.erase tables world stack records := by
  induction source with
  | nil => exact .nil
  | push tail ih => exact .push ih
  | blocked held saved tail ihSaved ihTail => exact .blocked held ihSaved ihTail
  | close unprotected summary saved tail ihSaved ihTail => exact .close unprotected summary.row_source ihSaved ihTail
  | spent tail ih => exact .spent ih

theorem LexicalSegment.row_store
    (source : LexicalSegment operations policy contracts tables families actions world
      stack input output demand requirements resumes dependencyScope incoming outgoing)
    (closing : UnwindRecords operations policy contracts tables world stack disposals)
    (known : contracts owner = some contract) :
    ClauseRowAdmission.SourceStore operations.erase owner contract.erase (resumes ++ disposals) :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, .legacy source.row_source,
    fun _ _ member => source.row_source.records_certified member, closing.row_source, contract_erase_known known, .refl _⟩


#print axioms Ash.OneShot.SourceDependencyFrames.LexicalFrame.row_source
#print axioms Ash.OneShot.SourceDependencyFrames.LexicalSegment.row_source
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindTemplate.row_source
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindRecords.row_source
#print axioms Ash.OneShot.SourceDependencyFrames.LexicalSegment.row_store
/-- The selected clause and operand retain exactly the requirement tree whose
row certificate is instantiated against the actual lexical allocation store. -/
theorem LexicalSegment.instantiate_clause
    (source : LexicalSegment operations policy contracts tables families actions world
      stack input output demand requirements resumes dependencyScope incoming outgoing)
    (closing : UnwindRecords operations policy contracts tables world stack disposals)
    (known : contracts owner = some contract)
    (body : Body operations policy contracts world allowed (.ticket binder owner)
      (environment.extend parameter argument) code answer
      ⟨owner, contract.erase, disposes, advertised⟩ dependencies)
    (operand : ValueSummary operations policy contracts world environment allowed value argument)
    (closed : ClosedValue value)
    (interface : ClauseRowAdmission.Interface owner contract.erase disposes (resumes ++ disposals)
      tail before requestRow)
    (exported : OwnerSource.exportAt tail before advertised = some requestRow) :
    ∃ clauseDemand, ∃ clauseRequirements : Requirements clauseDemand, ∃ row,
      Expression operations policy contracts world allowed (.ticket binder owner) environment
        (code.subst parameter value) answer clauseDemand clauseRequirements dependencies ∧
      RecursiveRequirements.Checked (resumes ++ disposals) (.live owner contract.held :: tail)
        before clauseRequirements row ∧ EffectBounds.Covers (requestRow ++ contract.resumeRow) row := by
  obtain ⟨_, _, expression, rows⟩ := body.normal_rows
  obtain ⟨row, checked, covered⟩ := rows.instantiate interface exported (source.row_store closing known)
  exact ⟨_, _, row, substitution expression operand closed, checked, covered⟩


#print axioms Ash.OneShot.SourceDependencyFrames.LexicalSegment.instantiate_clause
end Ash.OneShot.SourceDependencyFrames


namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations
open RecursiveRequirements (Requirements Store Checked evaluate)
open OwnerPhaseTransitions (Phases Trace spendAll)

/-- Finite effect checks for lexical closing requirements. Callback bounds
are interpreted at their actual suffix and phase. Retirement readiness is
supplied separately by the physical ownership trace. -/
inductive ClosingEffects (budget : Footprint) :
    OwnerPhases.Context → Phases → {demand : List Nat} → Requirements demand → Prop where
  | request (covered : raw ⊆ upper)
      (exported : OwnerSource.exportAt (nearer ++ receiving) before upper = some row)
      (bounded : row ⊆ budget) :
      ClosingEffects budget receiving before (.request nearer raw)
  | retire : ClosingEffects budget receiving before (.retire owner)
  | spent (consumed : before owner = .consumed) : ClosingEffects budget receiving before (.spent owner)
  | sequence (first : ClosingEffects budget receiving before (a : Requirements firstDemand))
      (second : ClosingEffects budget receiving (spendAll before firstDemand) b) :
      ClosingEffects budget receiving before (.sequence a b)

theorem ClosingEffects.prepend
    (source : ClosingEffects budget (prefixContext ++ receiving) before requirements) :
    ClosingEffects budget receiving before (requirements.prepend prefixContext) := by
  generalize contextSame : prefixContext ++ receiving = context at source
  induction source generalizing prefixContext receiving with
  | request covered exported bounded =>
      exact .request covered (by simpa only [← contextSame, List.append_assoc] using exported) bounded
  | retire => exact .retire
  | spent consumed => exact .spent consumed
  | sequence first second ihFirst ihSecond => exact .sequence (ihFirst contextSame) (ihSecond contextSame)

/-- Existing residual coverage and owner-trace decomposition suffice; no
new evaluator or assumption about later execution is used. -/
theorem ClosingEffects.checked
    (source : ClosingEffects budget receiving before (requirements : Requirements demand))
    (ownership : Trace before demand after) :
    ∃ row, Checked store receiving before requirements row ∧ row ⊆ budget := by
  induction source generalizing after with
  | request covered exported bounded =>
      obtain ⟨row, actual, within⟩ := UniformClauseBounds.residual_coverage covered exported
      exact ⟨row, .request actual, within.trans bounded⟩
  | retire => cases ownership with
    | cons ready rest => exact ⟨[], .retire ready, List.nil_subset _⟩
  | spent consumed => exact ⟨[], .spent consumed, List.nil_subset _⟩
  | sequence first second ihFirst ihSecond =>
      obtain ⟨middle, left, right⟩ := OwnerPhaseTransitions.trace_decompose ownership
      have same := OwnerPhaseTransitions.trace_result left
      subst middle
      obtain ⟨a, checkedA, boundA⟩ := ihFirst left
      obtain ⟨b, checkedB, boundB⟩ := ihSecond right
      exact ⟨a ++ b, .sequence checkedA checkedB, List.append_subset.mpr ⟨boundA, boundB⟩⟩

/-- Physical capture ownership establishes retirement legality. The remaining
source annotation consists of callback effect bounds and spent-marker checks. -/
theorem UnwindTemplate.checked_effects
    (summary : UnwindTemplate operations policy contracts tables world capture demand requirements)
    (effects : ClosingEffects budget receiving before requirements)
    (unique : (ownedTickets capture).Nodup)
    (ready : ∀ owner ∈ ownedTickets capture, before owner = .available) :
    ∃ row, evaluate entries receiving before requirements = some row ∧ row ⊆ budget := by
  have ownership := OwnerPhaseTransitions.trace_of_available (summary.ownership.symm.nodup unique)
    (fun owner member => ready owner (summary.ownership.mem_iff.mp member))
  obtain ⟨row, checked, covered⟩ := effects.checked (store := entries) ownership
  exact ⟨row, RecursiveRequirements.checked_complete checked, covered⟩

/-- The structural effect annotation loses no successfully checked lexical
closing template. Each leaf may use its exact row as its own upper bound. -/
theorem UnwindTemplate.effects_of_checked
    (summary : UnwindTemplate operations policy contracts tables world capture demand requirements)
    (checked : Checked entries receiving before requirements row)
    (bounded : row ⊆ budget) : ClosingEffects budget receiving before requirements := by
  induction summary generalizing receiving before row with
  | nil =>
      exact .request (List.Subset.refl _) ((evaluate_request_at).symm.trans (RecursiveRequirements.checked_complete checked)) bounded
  | plain tail ih | handler tail ih | cell tail ih => exact ih checked bounded
  | cleanup callback tail ih =>
      obtain ⟨a, b, first, second, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
      exact .sequence (.request (List.Subset.refl _)
        (evaluate_request_at.symm.trans (RecursiveRequirements.checked_complete first))
        ((List.subset_append_left _ _).trans bounded))
        (ih second ((List.subset_append_right _ _).trans bounded))
  | spent tail ih =>
      obtain ⟨a, b, first, second, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
      have evaluated := RecursiveRequirements.checked_complete first
      rw [RecursiveRecomposition.evaluate_spent] at evaluated
      split at evaluated
      · exact .sequence (.spent (by assumption)) (ih second ((List.subset_append_right _ _).trans bounded))
      · cases evaluated
  | retiring tail ih =>
      obtain ⟨a, b, first, second, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
      exact .sequence .retire (ih second ((List.subset_append_right _ _).trans bounded))
  | live saved tail ihSaved ihTail =>
      obtain ⟨a, b, first, second, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
      obtain ⟨c, d, retired, rest, rfl⟩ := RecursiveRequirements.checked_sequence_parts second
      have savedEffects := ihSaved (RecursiveRequirements.checked_prepend_iff.mp first)
        ((List.subset_append_left _ _).trans bounded)
      exact .sequence savedEffects.prepend
        (.sequence .retire (ihTail rest ((List.subset_append_right _ _).trans
          ((List.subset_append_right _ _).trans bounded))))

/-- The existing finite evaluator can check the structural annotation. Physical
ownership supplies all retirement checks; no source coverage is discarded. -/
theorem UnwindTemplate.effects_iff
    (summary : UnwindTemplate operations policy contracts tables world capture demand requirements)
    (unique : (ownedTickets capture).Nodup)
    (ready : ∀ owner ∈ ownedTickets capture, before owner = .available) :
    ClosingEffects budget receiving before requirements ↔
      ∃ row, evaluate entries receiving before requirements = some row ∧ row ⊆ budget := by
  constructor
  · exact fun effects => summary.checked_effects effects unique ready
  · rintro ⟨row, checked, bounded⟩
    exact summary.effects_of_checked (RecursiveRequirements.evaluate_sound checked) bounded

end Ash.OneShot.SourceDependencyFrames
#print axioms Ash.OneShot.SourceDependencyFrames.ClosingEffects.prepend
#print axioms Ash.OneShot.SourceDependencyFrames.ClosingEffects.checked
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindTemplate.checked_effects
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindTemplate.effects_of_checked
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindTemplate.effects_iff

namespace Ash.OneShot.SourceDependencyFrames.UnwindExamples
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements)
open InitialCleanupRouteGap

/-- The real callback's enclosing handlers discharge its checked upper row. -/
theorem retained_handler_effects : ClosingEffects [] [] OwnerPhaseTransitions.empty closingRequirements := by
  apply ClosingEffects.sequence
  · exact .request (List.Subset.refl _) (row := []) (by decide) (List.nil_subset _)
  · exact .request (List.Subset.refl _) (row := []) (by decide) (List.nil_subset _)

/-- The source effect annotation preserves the existing lexical-scope
counterexample: removing the handler cannot certify the empty budget. -/
theorem dropped_handler_effects_rejected :
    ¬ ClosingEffects [] [] OwnerPhaseTransitions.empty
      (.sequence (.request [] [⟨inner, 0, true⟩]) (.request [] [])) := by
  intro effects
  obtain ⟨row, checked, bounded⟩ := effects.checked (store := []) OwnerPhaseTransitions.Trace.nil
  have empty : row = [] := List.eq_nil_iff_forall_not_mem.mpr (fun _ member => List.not_mem_nil (bounded member))
  exact dropped_handler_not_closed (empty ▸ checked)

end Ash.OneShot.SourceDependencyFrames.UnwindExamples
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindExamples.retained_handler_effects
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindExamples.dropped_handler_effects_rejected

namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations
open RecursiveRequirements (Requirements Checked)
open OwnerPhaseTransitions (Trace spendAll)

/-- Reuse the existing six-case unwind preservation theorem to retain the
structural effect annotation after actual owner discharge. -/
theorem UnwindTemplate.advance_effects
    (source : UnwindTemplate operations policy contracts tables world stack demand requirements)
    (effects : ClosingEffects budget receiving before requirements)
    (ownership : Trace before demand completed)
    (step : LexicalUnwind.Advance stack after discharged) :
    ∃ nextDemand, ∃ nextRequirements : Requirements nextDemand,
      UnwindTemplate operations policy contracts tables world after nextDemand nextRequirements ∧
      ClosingEffects budget receiving (spendAll before (discharged.filterMap Syntax.ticketProjection)) nextRequirements := by
  obtain ⟨row, checked, covered⟩ := effects.checked (store := []) ownership
  obtain ⟨nextDemand, nextRequirements, summary, next⟩ := source.advance_checked step checked
  exact ⟨nextDemand, nextRequirements, summary, summary.effects_of_checked next covered⟩

/-- Callback entry receives its source body and effect budget while the
remaining unwind scopes retain their structural annotation. -/
theorem UnwindTemplate.start_cleanup_effects
    (source : UnwindTemplate operations policy contracts tables world
      (.push (.armed action) rest) demand requirements)
    (effects : ClosingEffects budget receiving before requirements)
    (ownership : Trace before demand completed) :
    ∃ latent dependencies callbackRow, ∃ tailRequirements : Requirements demand,
      Expression operations policy contracts world action.requests .none Environment.empty
        (.app action.action .unit) .unit []
        (.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent)
        (.sequence .pure (.sequence .pure dependencies)) ∧
      UnwindTemplate operations policy contracts tables world rest demand tailRequirements ∧
      Checked entries (OwnerPhases.ofStack tables (.push (.unwinding action) rest) ++ receiving) before
        (.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent) callbackRow ∧
      callbackRow ⊆ budget ∧ ClosingEffects budget receiving before tailRequirements := by
  obtain ⟨row, checked, covered⟩ := effects.checked (store := entries) ownership
  obtain ⟨latent, dependencies, callbackRow, tailRow, tailRequirements,
    callback, tail, callbackCheck, tailCheck, same⟩ := source.start_cleanup checked
  subst row
  exact ⟨latent, dependencies, callbackRow, tailRequirements, callback, tail, callbackCheck,
    (List.subset_append_left _ _).trans covered,
    tail.effects_of_checked tailCheck ((List.subset_append_right _ _).trans covered)⟩

end Ash.OneShot.SourceDependencyFrames
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindTemplate.advance_effects
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindTemplate.start_cleanup_effects

namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations
open RecursiveRequirements (Store)
variable {front capture tail : Stack}

/-- Recomposition moves existing lexical records and removes only the used
boundary's own optional disposal entry. Captured summaries remain unchanged. -/
theorem UnwindRecords.resume_split
    (source : UnwindRecords operations policy contracts tables world
      (front.append (.live owner input answer capture caller tail)) records) :
    ∃ removed nextRecords,
      UnwindRecords operations policy contracts tables world
        (capture.append (front.append (.spent owner answer caller tail))) nextRecords ∧
      records.Perm (removed ++ nextRecords) ∧
      (∀ entry ∈ removed, entry.1.owner = owner) := by
  obtain ⟨frontRecords, restRecords, first, boundary, same⟩ := source.split_append
  subst records
  cases boundary with
  | blocked held saved outside =>
      refine ⟨[], _, saved.append (first.append (.spent outside)), ?_, ?_⟩
      · simpa only [List.nil_append, List.append_assoc] using
          (List.perm_append_comm (l₁ := frontRecords) (l₂ := _)).append_right _
      · intro entry member; cases member
  | @close savedStack savedDemand savedReq nested tail remaining owner input answer caller unprotected summary saved outside =>
      refine ⟨[(⟨owner, .dispose⟩, ⟨savedDemand, savedReq⟩)], _,
        saved.append (first.append (.spent outside)), ?_, ?_⟩
      · have move := List.perm_middle
          (a := ((⟨owner, .dispose⟩, ⟨savedDemand, savedReq⟩) : RecursiveRequirements.Key × RecursiveRequirements.Template))
          (l₁ := frontRecords) (l₂ := nested ++ remaining)
        have exchange := (List.perm_append_comm (l₁ := frontRecords) (l₂ := nested)).append_right remaining
        have moved := move.trans (List.Perm.cons _ (by simpa only [List.append_assoc] using exchange))
        simpa only [List.cons_append, List.nil_append] using moved
      · intro entry member
        cases List.mem_singleton.mp member
        rfl

/-- Existing owner uniqueness makes the moved records equal, up to order,
to deletion of the consumed owner's entries. No new record is inferred. -/
theorem UnwindRecords.resume
    (source : UnwindRecords operations policy contracts tables world
      (front.append (.live owner input answer capture caller tail)) records)
    (unique : (ownedTickets (front.append (.live owner input answer capture caller tail))).Nodup) :
    ∃ nextRecords,
      UnwindRecords operations policy contracts tables world
        (capture.append (front.append (.spent owner answer caller tail))) nextRecords ∧
      (RecursiveTransport.removeOwner owner records).Perm nextRecords := by
  obtain ⟨removed, nextRecords, after, same, keys⟩ := source.resume_split
  have absent := (List.nodup_cons.mp
    (OwnerPhaseTransitions.resume_owned_permutation.nodup unique)).1
  have noRecord : owner ∉ RecursiveTransport.recordOwners nextRecords :=
    fun member => absent (after.owners_sublist.subset member)
  have filtered : RecursiveTransport.removeOwner owner (removed ++ nextRecords) = nextRecords := by
    rw [RecursiveRecomposition.remove_owner_filter, List.filter_append]
    have empty : removed.filter (fun entry => entry.1.owner != owner) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro entry member
      simp [keys entry member]
    rw [empty, List.nil_append, ← RecursiveRecomposition.remove_owner_filter,
      RecursiveRecomposition.remove_owner_absent noRecord]
  exact ⟨nextRecords, after, filtered ▸ RecursiveRecomposition.remove_owner_permutation same⟩
end Ash.OneShot.SourceDependencyFrames
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindRecords.resume_split
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindRecords.resume

namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations
open RecursiveRequirements (Requirements Store)
variable {front capture tail : Stack}

/-- The physical closing delimiter carries no continuation record. Reuse
resumption's record removal, then insert that actual delimiter. -/
theorem UnwindRecords.discard
    (source : UnwindRecords operations policy contracts tables world
      (front.append (.live owner input answer capture caller tail)) records)
    (unique : (ownedTickets (front.append (.live owner input answer capture caller tail))).Nodup) :
    ∃ nextRecords,
      UnwindRecords operations policy contracts tables world
        (capture.append (.push (.closing identity runtimeScope)
          (front.append (.spent owner answer caller tail)))) nextRecords ∧
      (RecursiveTransport.removeOwner owner records).Perm nextRecords := by
  obtain ⟨nextRecords, retained, permutation⟩ := source.resume unique
  obtain ⟨insideRecords, outsideRecords, inside, outside, same⟩ := retained.split_append
  exact ⟨insideRecords ++ outsideRecords, inside.append (.push outside), same ▸ permutation⟩

/-- Unique installation ownership identifies the stored closing summary
with this actual capture, rather than inferring a new summary at use. -/
theorem UnwindRecords.selected_template
    (source : UnwindRecords operations policy contracts tables world
      (front.append (.live owner input answer capture caller tail)) records)
    (unique : (ownedTickets (front.append (.live owner input answer capture caller tail))).Nodup)
    (found : RecursiveRequirements.lookup ⟨owner, .dispose⟩ records = some ⟨demand, requirements⟩) :
    ProtectionContexts.protectedMode capture.erase = false ∧
      UnwindTemplate operations policy contracts tables world capture demand requirements := by
  obtain ⟨actual, located, mode, unprotected, summary, balance⟩ := source.lookup_ownership found
  cases SourceTemplates.captured_in_unique unique located (RecursiveRecords.located_below front .here)
  exact ⟨unprotected, summary⟩
end Ash.OneShot.SourceDependencyFrames
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindRecords.discard
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindRecords.selected_template

namespace Ash.OneShot.SourceDependencyFrames.UnwindExamples
open ProtectionContracts ProtectionResiduals
open ProtectionResiduals.Examples (afterCompletion disposableF demandE)
open RecursiveRequirements (Requirements Checked evaluate)

/-- A retained handler may export an unprotected request, so the surviving
closing marker must be included in the independent cleanup-effect check. -/
theorem closing_delimiter_changes_check :
    let requirements : Requirements [] := .request [.ordinary afterCompletion] (qualify true demandE)
    Checked [] [.ordinary disposableF] OwnerPhaseTransitions.empty requirements [] ∧
    ¬ Checked [] [.ordinary (.barrier true), .ordinary disposableF]
      OwnerPhaseTransitions.empty requirements [] := by
  refine ⟨RecursiveRequirements.evaluate_sound (by
    simp only [evaluate, RecursiveRequirements.evaluateFuel]
    decide), ?_⟩
  intro checked
  have evaluated := RecursiveRequirements.checked_complete checked
  have rejected : evaluate [] [.ordinary (.barrier true), .ordinary disposableF]
      OwnerPhaseTransitions.empty (.request [.ordinary afterCompletion] (qualify true demandE)) = none := by
    simp only [evaluate, RecursiveRequirements.evaluateFuel]
    decide
  rw [rejected] at evaluated
  cases evaluated
end Ash.OneShot.SourceDependencyFrames.UnwindExamples
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindExamples.closing_delimiter_changes_check

namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution
open OwnerPhaseTransitions (available spendAll)

/-- Project existing physical owner accounting onto continuation owners and
reuse the established permutation and phase-consumption laws. -/
theorem unwind_owner_phases
    (step : LexicalUnwind.Advance before after discharged)
    (unique : (ownedTickets before).Nodup) :
    (ownedTickets after).Nodup ∧
      spendAll (available (ownedTickets before)) (discharged.filterMap Syntax.ticketProjection) =
        available (ownedTickets after) := by
  have accounted : (ownedTickets before).Perm
      ((discharged.filterMap Syntax.ticketProjection) ++ ownedTickets after) := by
    rw [owned_tickets_project, owned_tickets_project]
    exact ((LexicalUnwind.accounting step).filterMap Syntax.ticketProjection).trans
      (by rw [List.filterMap_append]; exact List.perm_append_comm)
  have nextUnique := accounted.nodup_iff.mp unique
  exact ⟨(List.nodup_append.mp nextUnique).2.1,
    (congrArg (fun phases => spendAll phases (discharged.filterMap Syntax.ticketProjection))
      (OwnerPhaseTransitions.available_permutation accounted)).trans
      (RecursiveClosing.spend_available_prefix nextUnique)⟩
end Ash.OneShot.SourceDependencyFrames
#print axioms Ash.OneShot.SourceDependencyFrames.unwind_owner_phases

namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution
open SourceDependencyAnnotations
open RecursiveRequirements (Store Requirements Checked)
open OwnerPhaseTransitions (available spendAll)

/-- The store update for an administrative unwind step. Opening a live capture
removes its callable records; its separate retirement marker still owns the
ticket. Other administrative steps leave the store unchanged. -/
def unwindStore (stack : Stack) (entries : Store) : Store :=
  match stack with
  | .live owner _ _ _ _ _ => RecursiveTransport.removeOwner owner entries
  | _ => entries

theorem unwind_store_sublist : (unwindStore stack entries).Sublist entries := by
  cases stack <;> first | exact List.Sublist.refl _ | exact RecursiveTransport.remove_owner_sublist

theorem unwind_store_combined : unwindStore stack (first ++ second) =
    unwindStore stack first ++ unwindStore stack second := by
  cases stack <;> first | rfl | exact RecursiveConsumption.remove_owner_append _ _ _

theorem unwind_store_outside (step : LexicalUnwind.Advance before after discharged) :
    unwindStore (before.append suffix) entries = unwindStore before entries := by
  cases step <;> rfl

private theorem child_records_absent
    (saved : UnwindRecords operations policy contracts tables world capture nested)
    (tail : UnwindRecords operations policy contracts tables world rest remaining)
    (absent : owner ∉ ownedTickets capture ++ ownedTickets rest) :
    owner ∉ RecursiveTransport.recordOwners (nested ++ remaining) := by
  intro member
  apply absent
  apply (saved.owners_sublist.append tail.owners_sublist).subset
  simpa only [RecursiveTransport.recordOwners, List.map_append] using member

/-- Every administrative case retains the exact old record payloads. Opening
a live capture removes only its own disposal entry, when present. -/
theorem UnwindRecords.advance
    (step : LexicalUnwind.Advance before after discharged)
    (source : UnwindRecords operations policy contracts tables world before records)
    (unique : (ownedTickets before).Nodup) :
    UnwindRecords operations policy contracts tables world after (unwindStore before records) := by
  cases step with
  | plain | handler | cell | retire => cases source with | push tail => exact tail
  | spent => cases source with | spent tail => exact tail
  | live => cases source with
    | blocked held saved tail =>
        have absent := child_records_absent saved tail (List.nodup_cons.mp unique).1
        simpa only [unwindStore, RecursiveRecomposition.remove_owner_absent absent] using
          saved.append (UnwindRecords.push tail)
    | close held summary saved tail =>
        have absent := child_records_absent saved tail (List.nodup_cons.mp unique).1
        simpa only [unwindStore, RecursiveTransport.removeOwner, if_pos rfl, if_true,
          RecursiveRecomposition.remove_owner_absent absent] using saved.append (UnwindRecords.push tail)

/-- The caller sees precisely its own availability map after the active
summary finishes, independently of the prefix's internal disposal order. -/
theorem UnwindTemplate.waiting_phases
    (summary : UnwindTemplate operations policy contracts tables world active demand requirements)
    (unique : (ownedTickets (active.append suffix)).Nodup) :
    spendAll (available (ownedTickets (active.append suffix))) demand = available (ownedTickets suffix) := by
  rw [PhaseRechecking.spendAll_permutation summary.ownership, owned_tickets_append]
  exact RecursiveClosing.spend_available_prefix (by simpa only [owned_tickets_append] using unique)

/-- Removing the opened capture's records cannot affect the waiting check:
that owner is already consumed at the phase boundary after the active prefix. -/
theorem unwind_waiting_checked
    (step : LexicalUnwind.Advance active next discharged)
    (unique : (ownedTickets (active.append suffix)).Nodup)
    (checked : Checked entries receiving (available (ownedTickets suffix)) requirements row) :
    Checked (unwindStore active entries) receiving (available (ownedTickets suffix)) requirements row := by
  cases step with
  | plain | handler | cell | spent | retire => exact checked
  | live =>
      apply RecursiveTransport.checked_remove_consumed checked
      have absent := (List.nodup_cons.mp unique).1
      apply if_neg
      intro member
      apply absent
      exact List.mem_append_right _ (by simpa only [owned_tickets_append] using List.mem_append_right _ member)
end Ash.OneShot.SourceDependencyFrames
#print axioms Ash.OneShot.SourceDependencyFrames.unwind_store_sublist
#print axioms Ash.OneShot.SourceDependencyFrames.unwind_store_combined
#print axioms Ash.OneShot.SourceDependencyFrames.unwind_store_outside
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindRecords.advance
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindTemplate.waiting_phases
#print axioms Ash.OneShot.SourceDependencyFrames.unwind_waiting_checked

namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution
open RecursiveRequirements (Store)

/-- Records belonging to the retained caller are unchanged by opening an
owner in the disjoint active prefix. -/
theorem unwind_waiting_records
    (step : LexicalUnwind.Advance active next discharged)
    (unique : (ownedTickets (active.append suffix)).Nodup)
    (included : RecursiveTransport.recordOwners records ⊆ ownedTickets suffix) :
    unwindStore active records = records := by
  cases step with
  | plain | handler | cell | spent | retire => rfl
  | live =>
      apply RecursiveRecomposition.remove_owner_absent
      intro member
      apply (List.nodup_cons.mp unique).1
      exact List.mem_append_right _ (by simpa only [owned_tickets_append] using (List.mem_append_right _ (included member)))
end Ash.OneShot.SourceDependencyFrames
#print axioms Ash.OneShot.SourceDependencyFrames.unwind_waiting_records

namespace Ash.OneShot.SourceDependencyFrames.UnwindExamples
open ScopedExpressions ScopedExecution
open RecursiveRequirements (Store)

/-- Record removal and ownership discharge occur at different transitions.
Opening retains ownership; only the later retirement pop discharges it. -/
theorem opening_before_retirement :
    let original : Stack := .live 19 .unit .unit .nil .none .nil
    let opened : Stack := .push (.retiring 19) .nil
    let records : Store := [(⟨19, .resume⟩, ⟨[], .request [] []⟩),
      (⟨19, .dispose⟩, ⟨[], .request [] []⟩)]
    LexicalUnwind.Advance original opened [] ∧
      ownedTickets opened = [19] ∧ unwindStore original records = [] ∧
      OwnerPhaseTransitions.available (ownedTickets opened) 19 = .available ∧
      LexicalUnwind.Advance opened .nil [.ticket 19] :=
  ⟨.live, rfl, rfl, rfl, .retire⟩
end Ash.OneShot.SourceDependencyFrames.UnwindExamples
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindExamples.opening_before_retirement

namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations
open RecursiveRequirements (Requirements evaluate)
open OwnerPhaseTransitions (spendAll)
private theorem unwind_source_reindex
    (source : UnwindSource operations policy contracts tables families world stack demand requirements dependencyScope)
    (same : demand = nextDemand) :
    ∃ next : Requirements nextDemand,
      UnwindSource operations policy contracts tables families world stack nextDemand next dependencyScope ∧
      ∀ store receiving before, evaluate store receiving before next = evaluate store receiving before requirements := by
  cases same
  exact ⟨requirements, source, fun _ _ _ => rfl⟩

/-- Enclosing-stack composition retains the interpretation suffix of every
    callback, including callbacks inside dormant captures. -/
theorem UnwindSource.append
    (first : UnwindSource operations policy contracts tables families world front a firstRequirements firstScope)
    (second : UnwindSource operations policy contracts tables families world tail b secondRequirements secondScope) :
    ∃ combined : Requirements (a ++ b),
      UnwindSource operations policy contracts tables families world (front.append tail) (a ++ b) combined (firstScope.append secondScope) ∧
      ∀ store receiving before, evaluate store receiving before combined =
        merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) before firstRequirements)
          (evaluate store receiving (spendAll before a) secondRequirements) := by
  induction first with
  | nil =>
      exact ⟨_, second, by intros; simp only [RecursiveRecomposition.evaluate_empty, spendAll,
        RecursiveRecomposition.merge_empty_left]⟩
  | plain next ih =>
      obtain ⟨combined, result, evaluation⟩ := ih
      exact ⟨_, .plain result, evaluation⟩
  | handler declaration next ih =>
      obtain ⟨combined, result, evaluation⟩ := ih
      exact ⟨_, .handler declaration result, evaluation⟩
  | cell next ih =>
      obtain ⟨combined, result, evaluation⟩ := ih
      exact ⟨_, .cell result, evaluation⟩
  | cleanup callback next ih =>
      obtain ⟨combined, result, evaluation⟩ := ih
      refine ⟨_, .cleanup callback result, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, evaluate_request_at,
        OwnerPhases.stack_append, List.append_assoc, evaluation, spendAll, List.nil_append, merge_assoc]
  | spent next ih =>
      obtain ⟨combined, result, evaluation⟩ := ih
      refine ⟨_, .spent result, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_spent,
        evaluation, spendAll, List.nil_append, merge_assoc]
  | retiring next ih =>
      obtain ⟨combined, result, evaluation⟩ := ih
      refine ⟨_, .retiring result, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveClosing.evaluate_retire,
        evaluation, spendAll, List.nil_append, List.cons_append, merge_assoc]
  | @live captured savedDemand savedRequirements savedScope rest tailDemand tailRequirements restScope owner input answer caller saved next ihSaved ihNext =>
      obtain ⟨combined, result, evaluation⟩ := ihNext
      obtain ⟨joined, rebuilt, reindexed⟩ := unwind_source_reindex
        (UnwindSource.live (owner := owner) (input := input) (answer := answer) (caller := caller) saved result)
        (nextDemand := (savedDemand ++ ([owner] ++ tailDemand)) ++ b) (by simp only [List.append_assoc])
      refine ⟨joined, rebuilt, ?_⟩
      intro store receiving before
      rw [reindexed]
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        RecursiveClosing.evaluate_retire, OwnerPhases.ofStack, OwnerPhases.stack_append,
        List.cons_append, List.append_assoc, evaluation, PhaseRechecking.spendAll_append, spendAll, merge_assoc]

/-- Each administrative unwind step preserves the checked effect row while
    spending exactly the continuation owners discharged by that runtime step. -/
theorem UnwindSource.advance_checked
    (source : UnwindSource operations policy contracts tables families world stack demand requirements dependencyScope)
    (step : LexicalUnwind.Advance stack after discharged)
    (checked : RecursiveRequirements.Checked entries receiving before requirements row) :
    ∃ nextDemand, ∃ nextRequirements : Requirements nextDemand,
      UnwindSource operations policy contracts tables families world after nextDemand nextRequirements dependencyScope.afterUnwind ∧
      RecursiveRequirements.Checked entries receiving
        (spendAll before (discharged.filterMap Syntax.ticketProjection)) nextRequirements row := by
  cases step with
  | plain => cases source with | plain tail => exact ⟨_, _, tail, checked⟩
  | handler => cases source with | handler declaration tail => exact ⟨_, _, tail, checked⟩
  | cell => cases source with | cell tail => exact ⟨_, _, tail, checked⟩
  | spent => cases source with
    | spent tail =>
      obtain ⟨firstRow, secondRow, first, second, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
      have firstEmpty : firstRow = [] := by
        have evaluated := RecursiveRequirements.checked_complete first
        rw [RecursiveRecomposition.evaluate_spent] at evaluated
        split at evaluated
        · exact (Option.some.inj evaluated).symm
        · cases evaluated
      subst firstRow
      exact ⟨_, _, tail, second⟩
  | retire => cases source with
    | retiring tail =>
      obtain ⟨firstRow, secondRow, first, second, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
      have firstEmpty : firstRow = [] := by
        have evaluated := RecursiveRequirements.checked_complete first
        rw [RecursiveClosing.evaluate_retire] at evaluated
        split at evaluated
        · exact (Option.some.inj evaluated).symm
        · cases evaluated
      subst firstRow
      exact ⟨_, _, tail, second⟩
  | live => cases source with
    | live saved tail =>
      obtain ⟨combined, result, evaluation⟩ := saved.append (UnwindSource.retiring tail)
      refine ⟨_, combined, result, RecursiveRequirements.evaluate_sound ?_⟩
      rw [evaluation]
      simpa only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        List.filterMap_nil, spendAll] using RecursiveRequirements.checked_complete checked

/-- Shared callback-entry calculation, independent of whether the retained
suffix is ordinary, abandoned or contains a closing delimiter. -/
theorem cleanup_application_checked
    (callback : ValueSummary operations policy contracts world Environment.empty [] action.action
      (.function .unit .unit action.requests latent dependencies))
    (checked : RecursiveRequirements.Checked entries receiving before
      (.request (OwnerPhases.ofStack tables rest) (qualify true latent)) callbackRow) :
    Expression operations policy contracts world action.requests .none Environment.empty
      (.app action.action .unit) .unit []
      (.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent)
      (.sequence .pure (.sequence .pure dependencies)) ∧
    RecursiveRequirements.Checked entries
      (OwnerPhases.ofStack tables (.push (.unwinding action) rest) ++ receiving) before
      (.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent) callbackRow := by
  have exported := RecursiveRequirements.checked_complete checked
  rw [evaluate_request_at] at exported
  have actual : OwnerSource.exportAt
      (OwnerPhases.ofStack tables (.push (.unwinding action) rest) ++ receiving) before latent = some callbackRow := by
    simpa only [OwnerPhases.ofStack, OwnerPhases.frameEntry, ExecFrame.erase, ActionData.erase,
      ProtectionContexts.frameProtected, OwnerPhaseTransitions.project, OwnerSource.exportAt,
      residualize, DisposalProtection.through_barrier, List.cons_append] using exported
  have pureCheck : RecursiveRequirements.Checked entries
      (OwnerPhases.ofStack tables (.push (.unwinding action) rest) ++ receiving) before (.request [] []) [] :=
    .request (by simp [OwnerSource.exportAt, residual_empty])
  exact ⟨.app (Values.change_context callback action.closed.1 action.requests .none) .unit (List.Subset.refl _),
    .emitAfter (.sequence pureCheck pureCheck) actual⟩

/-- The summary's leading cleanup row is exactly the row checked for the
    real callback application under the actual unwinding marker. -/
theorem UnwindSource.start_cleanup
    (source : UnwindSource operations policy contracts tables families world
      (.push (.armed action) rest) demand requirements dependencyScope)
    (checked : RecursiveRequirements.Checked entries receiving before requirements row) :
    ∃ latent dependencies callbackRow tailRow nextScope, ∃ tailRequirements : Requirements demand,
      dependencyScope = .cleanup action.requests dependencies nextScope ∧
      Expression operations policy contracts world action.requests .none Environment.empty
        (.app action.action .unit) .unit []
        (.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent)
        (.sequence .pure (.sequence .pure dependencies)) ∧
      UnwindSource operations policy contracts tables families world rest demand tailRequirements nextScope ∧
      RecursiveRequirements.Checked entries
        (OwnerPhases.ofStack tables (.push (.unwinding action) rest) ++ receiving) before
        (.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent) callbackRow ∧
      RecursiveRequirements.Checked entries receiving before tailRequirements tailRow ∧
      row = callbackRow ++ tailRow := by
  cases source with
  | @cleanup latent dependencies rest demand requirements restScope action callback tail =>
      obtain ⟨callbackRow, tailRow, callbackCheck, tailCheck, same⟩ :=
        RecursiveRequirements.checked_sequence_parts checked
      obtain ⟨expression, application⟩ := cleanup_application_checked callback callbackCheck
      exact ⟨_, _, callbackRow, tailRow, _, _, rfl, expression, tail, application, tailCheck, same⟩


end Ash.OneShot.SourceDependencyFrames
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindSource.append
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindSource.advance_checked
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindSource.start_cleanup

namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution
open SourceDependencyAnnotations
open RecursiveRequirements (Requirements Checked)
open OwnerPhaseTransitions (Trace spendAll)

/-- Preserve the authenticated callback annotations along with the effect
summary, using the same finite requirement evaluation and ownership trace. -/
theorem UnwindSource.advance_effects
    (source : UnwindSource operations policy contracts tables families world stack demand requirements dependencyScope)
    (effects : ClosingEffects budget receiving before requirements)
    (ownership : Trace before demand completed)
    (step : LexicalUnwind.Advance stack after discharged) :
    ∃ nextDemand, ∃ nextRequirements : Requirements nextDemand,
      UnwindSource operations policy contracts tables families world after nextDemand nextRequirements dependencyScope.afterUnwind ∧
      ClosingEffects budget receiving (spendAll before (discharged.filterMap Syntax.ticketProjection)) nextRequirements := by
  obtain ⟨row, checked, covered⟩ := effects.checked (store := []) ownership
  obtain ⟨nextDemand, nextRequirements, next, nextCheck⟩ := source.advance_checked step checked
  exact ⟨nextDemand, nextRequirements, next, next.template.effects_of_checked nextCheck covered⟩

/-- Cleanup entry exposes the exact dependency annotation authenticated by
its source derivation, together with the already checked actual effect budget. -/
theorem UnwindSource.start_cleanup_effects
    (source : UnwindSource operations policy contracts tables families world
      (.push (.armed action) rest) demand requirements dependencyScope)
    (effects : ClosingEffects budget receiving before requirements)
    (ownership : Trace before demand completed) :
    ∃ latent dependencies callbackRow nextScope, ∃ tailRequirements : Requirements demand,
      dependencyScope = .cleanup action.requests dependencies nextScope ∧
      Expression operations policy contracts world action.requests .none Environment.empty
        (.app action.action .unit) .unit []
        (.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent)
        (.sequence .pure (.sequence .pure dependencies)) ∧
      UnwindSource operations policy contracts tables families world rest demand tailRequirements nextScope ∧
      Checked entries (OwnerPhases.ofStack tables (.push (.unwinding action) rest) ++ receiving) before
        (.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent) callbackRow ∧
      callbackRow ⊆ budget ∧ ClosingEffects budget receiving before tailRequirements := by
  obtain ⟨row, checked, covered⟩ := effects.checked (store := entries) ownership
  obtain ⟨latent, dependencies, callbackRow, tailRow, nextScope, tailRequirements,
    annotation, callback, tail, callbackCheck, tailCheck, same⟩ := source.start_cleanup checked
  subst row
  exact ⟨latent, dependencies, callbackRow, nextScope, tailRequirements, annotation, callback, tail, callbackCheck,
    (List.subset_append_left _ _).trans covered,
    tail.template.effects_of_checked tailCheck ((List.subset_append_right _ _).trans covered)⟩
end Ash.OneShot.SourceDependencyFrames
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindSource.advance_effects
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindSource.start_cleanup_effects


namespace Ash.OneShot.SourceDependencyFrames
open SourceDependencyAnnotations
/-- Fresh continuation allocation preserves the same source-derived closing
    record. No callback or lexical interpretation is replaced. -/
theorem UnwindSource.transport
    (source : UnwindSource operations policy contracts tables families world stack demand requirements dependencyScope)
    (extension : contracts.Extends nextContracts) (larger : world ⊆ nextWorld) :
    UnwindSource operations policy nextContracts tables families nextWorld stack demand requirements dependencyScope := by
  induction source with
  | nil => exact .nil
  | plain next ih => exact .plain ih
  | handler declaration next ih => exact .handler (declaration.transport extension larger) ih
  | cell next ih => exact .cell ih
  | cleanup callback next ih => exact .cleanup (expression_transport callback extension larger) ih
  | live saved next ihSaved ihNext => exact .live ihSaved ihNext
  | spent next ih => exact .spent ih
  | retiring next ih => exact .retiring ih

end Ash.OneShot.SourceDependencyFrames
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindSource.transport


namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution

/-- Cell payload updates leave dormant captures and their stored bodies intact. -/
theorem UnwindRecords.cell_update
    (update : CellUpdate identity old new before after)
    (source : UnwindRecords operations policy contracts tables world before records) :
    UnwindRecords operations policy contracts tables world after records := by
  induction update generalizing records with
  | hit => cases source with | push tail => exact .push tail
  | push miss next ih => cases source with | push tail => exact .push (ih tail)
  | live next ih => cases source with
    | blocked held saved tail => exact .blocked held saved (ih tail)
    | close held summary saved tail => exact .close held summary saved (ih tail)
  | spent next ih => cases source with | spent tail => exact .spent (ih tail)

/-- Ordinary evaluation without continuation capture derives its surviving records.
Resumption reuses exact owner removal; all other cases retain the same entries.
The excluded legacy discard rule is not a lexical runtime transition. -/
theorem UnwindRecords.ordinary_step
    (step : RawStep before after created discharged)
    (ordinary : LexicalUnwind.ordinary before.expression)
    (noCapture : ∀ owner, Owner.ticket owner ∉ created)
    (source : UnwindRecords operations policy contracts tables world before.stack records)
    (unique : (ownedTickets before.stack).Nodup) :
    ∃ retained, UnwindRecords operations policy contracts tables world after.stack retained ∧ retained ⊆ records := by
  cases step with
  | focus | enterHandler | enterCell | enterCleanup => exact ⟨_, .push source, List.Subset.refl _⟩
  | plug | leaveHandler | leaveCell | finishCleanup | finishClose | retire =>
      cases source with | push tail => exact ⟨_, tail, List.Subset.refl _⟩
  | startCleanup => cases source with | push tail => exact ⟨_, .push tail, List.Subset.refl _⟩
  | bind | beta | ifTrue | ifFalse => exact ⟨_, source, List.Subset.refl _⟩
  | leaveClause => cases source with | spent tail => exact ⟨_, tail, List.Subset.refl _⟩
  | capture => exact False.elim (noCapture _ List.mem_cons_self)
  | discard => exact False.elim ordinary
  | resume =>
      obtain ⟨retained, next, permutation⟩ := source.resume unique
      exact ⟨retained, next, fun _ member => RecursiveTransport.remove_owner_sublist.subset
        (permutation.mem_iff.mpr member)⟩
  | readCell identity payload scope before after update => exact ⟨_, source.cell_update update, List.Subset.refl _⟩
  | writeCell identity old new scope before after update => exact ⟨_, source.cell_update update, List.Subset.refl _⟩
end Ash.OneShot.SourceDependencyFrames
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindRecords.cell_update
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindRecords.ordinary_step



namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution
open SourceDependencyAnnotations
open RecursiveRequirements (Requirements)

/-- A handler remains a callable interpretation while its enclosing scopes
are being abandoned. Its actual rich declaration is retained independently of
normal pending-code effect composition. -/
theorem UnwindSource.handler_source
    {handler : HandlerData}
    (cut : HandlerCut requested whole capture tail handler)
    (source : UnwindSource operations policy contracts tables families world whole demand requirements dependencyScope) :
    ∃ answer residual, Frame operations policy contracts tables families world
      (.handler handler) answer answer [] (.request [] [])
      (.handler handler.effectInst (tables handler) (families handler)) (handler.effectInst :: residual) residual := by
  induction cut generalizing demand dependencyScope with
  | hit handler tail same => cases source with
      | handler declaration tail => exact ⟨_, _, declaration⟩
  | push frame rest captured tail handler miss next ih =>
      cases source <;> apply ih <;> assumption
  | live owner input answer saved caller rest captured tail handler next ih =>
      cases source with | live saved tail => exact ih tail
  | spent owner answer caller rest captured tail handler next ih =>
      cases source with | spent tail => exact ih tail
end Ash.OneShot.SourceDependencyFrames
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindSource.handler_source



namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations
open RecursiveRequirements (Requirements evaluate)
open OwnerPhaseTransitions (spendAll)
open ProtectionResiduals
open RecursiveRecomposition (evaluate_empty evaluate_spent merge_empty_left)

/-- A rich value is expected only when execution reaches a scope normally.
Unwinding crosses scopes without supplying an abandoned result value. -/
inductive ModeValue where
  | value (type : Value)
  | unwind

def ModeValue.mode : ModeValue → LexicalUnwind.UseMode
  | .value _ => .ordinary
  | .unwind => .unwind

/-- Source for one actual frame, at its actual execution mode. Ordinary
frames reuse rich source typing; skipped frames contribute no ordinary work.
Whole-stack request checking remains contextual at the requirement judgment. -/
inductive ModeSourceFrame (operations : Operations) (policy : Syntax.TicketPolicy)
    (contracts : Contracts) (tables : CallableProtectionFrames.Tables) (families : Families) (world : List Nat) :
    ExecFrame → ModeValue → ModeValue → (demand : List Nat) → Requirements demand →
      (DependencyScope → DependencyScope) → Prop where
  | ordinary (source : Frame operations policy contracts tables families world entry input output demand requirements layer incoming outgoing) :
      ModeSourceFrame operations policy contracts tables families world entry (.value input) (.value output) demand requirements layer
  | unwinding (callback : ValueSummary operations policy contracts world Environment.empty [] action.action
      (.function .unit .unit action.requests latent dependencies)) :
      ModeSourceFrame operations policy contracts tables families world (.unwinding action) (.value .unit) .unwind
        [] (.request [] []) .running
  | closing (scope : ScopedPorts.EffectScopeKnown contracts.erase.ports caller) :
      ModeSourceFrame operations policy contracts tables families world (.closing identity caller) input (.value .unit)
        [] (.request [] []) .running
  | retiring : ModeSourceFrame operations policy contracts tables families world (.retiring owner) input input
        [owner] (.retire owner) .running
  | skipped : ModeSourceFrame operations policy contracts tables families world (.plain data) .unwind .unwind
        [] (.request [] []) (.plain dependencies)
  | handler (source : Frame operations policy contracts tables families world (.handler data) answer answer [] (.request [] [])
        (.handler data.effectInst (tables data) (families data)) (data.effectInst :: residual) residual) :
      ModeSourceFrame operations policy contracts tables families world (.handler data) .unwind .unwind
        [] (.request [] []) (.handler data.effectInst (tables data) (families data))
  | cell : ModeSourceFrame operations policy contracts tables families world (.cell identity payload caller answer) .unwind .unwind
        [] (.request [] []) (.cell identity)
  | cleanup (callback : ValueSummary operations policy contracts world Environment.empty [] action.action
        (.function .unit .unit action.requests latent dependencies)) :
      ModeSourceFrame operations policy contracts tables families world (.armed action) .unwind .unwind
        [] (.request [] (qualify true latent)) (.cleanup action.requests dependencies)

/-- Rich source requirements follow the actual return mode. Dormant ordinary
captures retain their checked source; opening an abandoned capture contributes
its cleanup requirements and the owner's retirement. Store certificates and
continuation permissions are separate facets, as in the existing source rules. -/
inductive ModeSource (operations : Operations) (policy : Syntax.TicketPolicy)
    (contracts : Contracts) (tables : CallableProtectionFrames.Tables) (families : Families)
    (actions : Syntax.UsageTickets) (world : List Nat) :
    Stack → ModeValue → ModeValue → (demand : List Nat) → Requirements demand → DependencyScope → Prop where
  | nil : ModeSource operations policy contracts tables families actions world .nil input input [] (.request [] []) .nil
  | push (head : ModeSourceFrame operations policy contracts tables families world entry input middle firstDemand first layer)
      (tail : ModeSource operations policy contracts tables families actions world rest middle output tailDemand second restScope) :
      ModeSource operations policy contracts tables families actions world (.push entry rest) input output
        (firstDemand ++ tailDemand) (.sequence (first.prepend (OwnerPhases.ofStack tables rest)) second) (layer restScope)
  | live (known : contracts owner = some contract) (actionKnown : actions owner = some rights)
      (inputAnnotation : contract.input.erase.port = ScopedPorts.eraseType inputType)
      (answerAnnotation : contract.answer.erase.port = ScopedPorts.eraseType answerType)
      (callerScope : ScopedPorts.EffectScopeKnown contracts.erase.ports caller)
      (held : contract.held = ProtectionContexts.protectedMode captured.erase)
      (saved : ModeSource operations policy contracts tables families actions world
        captured (.value contract.input) boundary contract.resumeDemand body savedScope)
      (answer : boundary = .value contract.answer ∨ boundary = .unwind)
      (tail : ModeSource operations policy contracts tables families actions world rest boundary output demand requirements restScope) :
      ModeSource operations policy contracts tables families actions world (.live owner inputType answerType captured caller rest)
        (.value contract.answer) output demand (.sequence (.spent owner) requirements) (.live owner savedScope restScope)
  | opening (saved : ModeSource operations policy contracts tables families actions world captured .unwind .unwind savedDemand savedRequirements savedScope)
      (tail : ModeSource operations policy contracts tables families actions world rest .unwind output tailDemand tailRequirements restScope) :
      ModeSource operations policy contracts tables families actions world (.live owner input answer captured caller rest)
        .unwind output (savedDemand ++ ([owner] ++ tailDemand))
        (.sequence (savedRequirements.prepend (OwnerPhases.ofStack tables (.push (.retiring owner) rest)))
          (.sequence (.retire owner) tailRequirements)) (.live owner savedScope restScope)
  | spent (known : contracts owner = some contract)
      (annotation : contract.answer.erase.port = ScopedPorts.eraseType answerType)
      (callerScope : ScopedPorts.EffectScopeKnown contracts.erase.ports caller)
      (tail : ModeSource operations policy contracts tables families actions world rest (.value contract.answer) output demand requirements restScope) :
      ModeSource operations policy contracts tables families actions world (.spent owner answerType caller rest)
        (.value contract.answer) output demand (.sequence (.spent owner) requirements) (.spent owner restScope)
  | skippedSpent (tail : ModeSource operations policy contracts tables families actions world rest .unwind output demand requirements restScope) :
      ModeSource operations policy contracts tables families actions world (.spent owner answerType caller rest)
        .unwind output demand (.sequence (.spent owner) requirements) (.spent owner restScope)

theorem ModeSourceFrame.realizes
    (source : ModeSourceFrame operations policy contracts tables families world entry input output demand requirements layer) :
    SourceDependencyCapture.Frame tables families layer entry := by
  cases source with
  | ordinary source => exact source.realizes
  | unwinding => exact .unwinding
  | closing => exact .closing
  | retiring => exact .retiring
  | skipped => exact .plain
  | handler => exact .handler
  | cell => exact .cell
  | cleanup => exact .cleanup

theorem ModeSource.realizes
    (source : ModeSource operations policy contracts tables families actions world stack input output demand requirements scope) :
    SourceDependencyCapture.Realizes tables families scope stack := by
  induction source with
  | nil => exact .nil
  | push head tail ih => exact .push head.realizes ih
  | live known rights inputAnnotation answerAnnotation caller held saved answer tail ihSaved ihTail => exact .live ihSaved ihTail
  | opening saved tail ihSaved ihTail => exact .live ihSaved ihTail
  | spent known annotation caller tail ih | skippedSpent tail ih => exact .spent ih

/-- The ordinary source fragment embeds without weakening its rich value or
requirement annotations. Its effect interface remains independent evidence. -/
theorem Segment.mode_source
    (source : Segment operations policy contracts tables families actions world
      stack input output demand requirements records scope incoming outgoing) :
    ModeSource operations policy contracts tables families actions world stack (.value input) (.value output) demand requirements scope := by
  induction source with
  | nil => exact .nil
  | push head tail bound ih => exact .push (.ordinary head) ih
  | live known rights inputAnnotation answerAnnotation caller held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live known rights inputAnnotation answerAnnotation caller held ihSaved (.inl rfl) ihTail
  | spent known annotation caller tail bound ih => exact .spent known annotation caller ih

/-- Source recomposition reuses the existing requirement evaluation algebra.
Only the actual mode/value boundary must match; skipped code adds no effects. -/
theorem ModeSource.append
    (first : ModeSource operations policy contracts tables families actions world front input middle
      firstDemand firstRequirements firstScope)
    (second : ModeSource operations policy contracts tables families actions world tail middle output
      secondDemand secondRequirements secondScope) :
    ∃ combined : Requirements (firstDemand ++ secondDemand),
      ModeSource operations policy contracts tables families actions world (front.append tail) input output
        (firstDemand ++ secondDemand) combined (firstScope.append secondScope) ∧
      ∀ store receiving phases,
        evaluate store receiving phases combined =
          merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) phases firstRequirements)
            (evaluate store receiving (spendAll phases firstDemand) secondRequirements) := by
  induction first generalizing output secondDemand secondRequirements secondScope tail with
  | nil => exact ⟨secondRequirements, second, by intros; simp only [evaluate_empty, spendAll, merge_empty_left]⟩
  | push head rest ih =>
      obtain ⟨combined, source, evaluation⟩ := ih second
      rw [List.append_assoc]
      have rebuilt := ModeSource.push head source
      rw [← head.realizes.append] at rebuilt
      refine ⟨_, rebuilt, ?_⟩
      intro store receiving phases
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        OwnerPhases.stack_append, List.append_assoc, evaluation, PhaseRechecking.spendAll_append, merge_assoc]
  | live known rights inputAnnotation answerAnnotation caller held saved answer rest ihSaved ihRest =>
      obtain ⟨combined, source, evaluation⟩ := ihRest second
      refine ⟨_, .live known rights inputAnnotation answerAnnotation caller held saved answer source, ?_⟩
      intro store receiving phases
      simp only [RecursiveRequirements.evaluate_sequence, evaluate_spent, evaluation, spendAll, merge_assoc]
  | opening saved rest ihSaved ihRest =>
      obtain ⟨combined, source, evaluation⟩ := ihRest second
      rw [List.append_assoc, List.append_assoc]
      refine ⟨_, .opening saved source, ?_⟩
      intro store receiving phases
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        OwnerPhases.stack_append, OwnerPhases.ofStack, List.cons_append, List.append_assoc, evaluation,
        PhaseRechecking.spendAll_append, merge_assoc, RecursiveClosing.evaluate_retire, spendAll, List.nil_append]
  | spent known annotation caller rest ih =>
      obtain ⟨combined, source, evaluation⟩ := ih second
      refine ⟨_, .spent known annotation caller source, ?_⟩
      intro store receiving phases
      simp only [RecursiveRequirements.evaluate_sequence, evaluate_spent, evaluation, spendAll, merge_assoc]
  | skippedSpent rest ih =>
      obtain ⟨combined, source, evaluation⟩ := ih second
      refine ⟨_, .skippedSpent source, ?_⟩
      intro store receiving phases
      simp only [RecursiveRequirements.evaluate_sequence, evaluate_spent, evaluation, spendAll, merge_assoc]

/-- Embed the existing abandoned-source proof. Empty administrative nodes
may insert empty sequencing nodes; their requirement evaluation is identical. -/
theorem UnwindSource.mode_source
    (source : UnwindSource operations policy contracts tables families world stack demand requirements scope) :
    ∃ next : Requirements demand,
      ModeSource operations policy contracts tables families actions world stack .unwind .unwind demand next scope ∧
      ∀ store receiving phases, evaluate store receiving phases next = evaluate store receiving phases requirements := by
  induction source with
  | nil => exact ⟨_, .nil, by intros; rfl⟩
  | plain tail ih =>
      obtain ⟨next, source, same⟩ := ih
      refine ⟨_, .push .skipped source, ?_⟩
      intro store receiving phases
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        evaluate_empty, spendAll, merge_empty_left, same]
  | handler declaration tail ih =>
      obtain ⟨next, source, same⟩ := ih
      refine ⟨_, .push (.handler declaration) source, ?_⟩
      intro store receiving phases
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        evaluate_empty, spendAll, merge_empty_left, same]
  | cell tail ih =>
      obtain ⟨next, source, same⟩ := ih
      refine ⟨_, .push .cell source, ?_⟩
      intro store receiving phases
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        evaluate_empty, spendAll, merge_empty_left, same]
  | cleanup callback tail ih =>
      obtain ⟨next, source, same⟩ := ih
      refine ⟨_, .push (.cleanup callback) source, ?_⟩
      intro store receiving phases
      simp only [Requirements.prepend, List.nil_append, RecursiveRequirements.evaluate_sequence, same]
  | live saved tail ihSaved ihTail =>
      obtain ⟨first, inside, sameInside⟩ := ihSaved
      obtain ⟨second, outside, sameOutside⟩ := ihTail
      refine ⟨_, .opening inside outside, ?_⟩
      intro store receiving phases
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, sameInside, sameOutside]
  | spent tail ih =>
      obtain ⟨next, source, same⟩ := ih
      refine ⟨_, .skippedSpent source, ?_⟩
      intro store receiving phases
      simp only [RecursiveRequirements.evaluate_sequence, same]
  | retiring tail ih =>
      obtain ⟨next, source, same⟩ := ih
      refine ⟨_, .push .retiring source, ?_⟩
      intro store receiving phases
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
        RecursiveClosing.evaluate_retire, same]

/-- The mode is fixed by actual runtime markers, independently of rich source
annotations or the evaluation of any requirement row. -/
theorem ModeSource.return_mode
    (source : ModeSource operations policy contracts tables families actions world stack input output demand requirements scope) :
    LexicalUnwind.returnMode stack input.mode = output.mode := by
  induction source with
  | nil => rfl
  | push head tail ih => cases head with
      | ordinary frame => cases frame <;> exact ih
      | unwinding | closing | retiring | skipped | handler | cell | cleanup => exact ih
  | live known rights inputAnnotation answerAnnotation caller held saved answer tail ihSaved ihTail =>
      simpa only [ModeValue.mode, LexicalUnwind.returnMode] using
        (show LexicalUnwind.returnMode _ (LexicalUnwind.returnMode _ .ordinary) = _ from
          by rw [show LexicalUnwind.returnMode _ .ordinary = _ from ihSaved]; exact ihTail)
  | opening saved tail ihSaved ihTail =>
      simpa only [LexicalUnwind.returnMode, ihSaved] using ihTail
  | spent known annotation caller tail ih | skippedSpent tail ih => exact ih

/-- Decompose the rich source at the actual runtime stack boundary. The
same contextual requirement algebra used by recomposition gives the split. -/
theorem ModeSource.split
    (source : ModeSource operations policy contracts tables families actions world
      (front.append tail) input output demand requirements scope) :
    ∃ (middle : ModeValue) (firstDemand secondDemand : List Nat),
    ∃ firstRequirements : Requirements firstDemand, ∃ secondRequirements : Requirements secondDemand,
    ∃ firstScope secondScope,
      ModeSource operations policy contracts tables families actions world front input middle firstDemand firstRequirements firstScope ∧
      ModeSource operations policy contracts tables families actions world tail middle output secondDemand secondRequirements secondScope ∧
      scope = firstScope.append secondScope ∧ demand = firstDemand ++ secondDemand ∧
      ∀ store receiving phases,
        evaluate store receiving phases requirements =
          merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) phases firstRequirements)
            (evaluate store receiving (spendAll phases firstDemand) secondRequirements) := by
  induction front generalizing input demand requirements scope with
  | nil =>
      refine ⟨input, [], demand, .request [] [], requirements, .nil, scope, .nil, source, rfl, rfl, ?_⟩
      intro store receiving phases
      simp only [evaluate_empty, spendAll, merge_empty_left]
  | push entry rest ih => cases source with
      | push head remaining =>
          obtain ⟨middle, firstDemand, secondDemand, firstRequirements, secondRequirements,
            firstScope, secondScope, first, second, sameScope, sameDemand, evaluation⟩ := ih remaining
          subst sameScope
          refine ⟨middle, _, secondDemand, _, secondRequirements, _, secondScope,
            .push head first, second, head.realizes.append.symm, ?_, ?_⟩
          · simp only [sameDemand, List.append_assoc]
          · intro store receiving phases
            simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
              OwnerPhases.stack_append, List.append_assoc, evaluation, PhaseRechecking.spendAll_append, merge_assoc]
  | live owner inputType answerType saved caller rest ihSaved ihRest => cases source with
      | live known rights inputAnnotation answerAnnotation scope held captured answer remaining =>
          obtain ⟨middle, firstDemand, secondDemand, firstRequirements, secondRequirements,
            firstScope, secondScope, first, second, sameScope, sameDemand, evaluation⟩ := ihRest remaining
          subst sameScope
          refine ⟨middle, firstDemand, secondDemand, _, secondRequirements, _, secondScope,
            .live known rights inputAnnotation answerAnnotation scope held captured answer first,
            second, rfl, sameDemand, ?_⟩
          intro store receiving phases
          simp only [RecursiveRequirements.evaluate_sequence, evaluate_spent, evaluation, spendAll, merge_assoc]
      | opening captured remaining =>
          obtain ⟨middle, firstDemand, secondDemand, firstRequirements, secondRequirements,
            firstScope, secondScope, first, second, sameScope, sameDemand, evaluation⟩ := ihRest remaining
          subst sameScope
          refine ⟨middle, _, secondDemand, _, secondRequirements, _, secondScope,
            .opening captured first, second, rfl, ?_, ?_⟩
          · simp only [sameDemand, List.append_assoc]
          · intro store receiving phases
            simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
              OwnerPhases.stack_append, OwnerPhases.ofStack, List.cons_append, List.append_assoc, evaluation,
              PhaseRechecking.spendAll_append, merge_assoc, RecursiveClosing.evaluate_retire, spendAll, List.nil_append]
  | spent owner answerType caller rest ih => cases source with
      | spent known annotation scope remaining =>
          obtain ⟨middle, firstDemand, secondDemand, firstRequirements, secondRequirements,
            firstScope, secondScope, first, second, sameScope, sameDemand, evaluation⟩ := ih remaining
          subst sameScope
          refine ⟨middle, firstDemand, secondDemand, _, secondRequirements, _, secondScope,
            .spent known annotation scope first, second, rfl, sameDemand, ?_⟩
          intro store receiving phases
          simp only [RecursiveRequirements.evaluate_sequence, evaluate_spent, evaluation, spendAll, merge_assoc]
      | skippedSpent remaining =>
          obtain ⟨middle, firstDemand, secondDemand, firstRequirements, secondRequirements,
            firstScope, secondScope, first, second, sameScope, sameDemand, evaluation⟩ := ih remaining
          subst sameScope
          refine ⟨middle, firstDemand, secondDemand, _, secondRequirements, _, secondScope,
            .skippedSpent first, second, rfl, sameDemand, ?_⟩
          intro store receiving phases
          simp only [RecursiveRequirements.evaluate_sequence, evaluate_spent, evaluation, spendAll, merge_assoc]

/-- At a terminal handler cut the retained result boundary is either that
handler's rich answer or abandonment. The handler declaration is the witness
stored in the same source derivation. -/
theorem ModeSource.handler_result {handler : HandlerData}
    (cut : HandlerCut requested whole captured tail handler)
    (source : ModeSource operations policy contracts tables families actions world whole input output demand requirements scope)
    (empty : tail = .nil) :
    ∃ (answer : Value) (residual : List Instance),
      Frame operations policy contracts tables families world (.handler handler) answer answer [] (.request [] [])
        (.handler handler.effectInst (tables handler) (families handler)) (handler.effectInst :: residual) residual ∧
      (output = .value answer ∨ output = .unwind) := by
  induction cut generalizing input demand requirements scope with
  | hit handler tail same =>
      subst tail
      cases source with
      | push head rest =>
          cases rest
          cases head with
          | ordinary frame => cases frame with
              | handler caller annotation clauses coverage unique declarations capabilities modes =>
                  exact ⟨_, _, .handler caller annotation clauses coverage unique declarations capabilities modes, .inl rfl⟩
          | handler frame => exact ⟨_, _, frame, .inr rfl⟩
  | push frame rest captured tail handler miss next ih => cases source with
      | push head remaining => exact ih remaining empty
  | live owner inputType answerType saved caller rest captured tail handler next ih => cases source with
      | live known rights inputAnnotation answerAnnotation caller held saved answer remaining => exact ih remaining empty
      | opening saved remaining => exact ih remaining empty
  | spent owner answerType caller rest captured tail handler next ih => cases source with
      | spent known annotation caller remaining => exact ih remaining empty
      | skippedSpent remaining => exact ih remaining empty

/-- Handler capture follows the same split, even when the captured fragment
contains an unwind-return marker. No ordinary requirements are imposed on its
abandoned suffix. -/
theorem ModeSource.handler_cut
    (cut : HandlerCut requested whole captured tail handler)
    (source : ModeSource operations policy contracts tables families actions world whole input output demand requirements scope) :
    ∃ (answer : Value) (residual : List Instance) (middle : ModeValue) (firstDemand secondDemand : List Nat),
    ∃ firstRequirements : Requirements firstDemand, ∃ secondRequirements : Requirements secondDemand,
    ∃ firstScope secondScope,
      Frame operations policy contracts tables families world (.handler handler) answer answer [] (.request [] [])
        (.handler handler.effectInst (tables handler) (families handler)) (handler.effectInst :: residual) residual ∧
      (middle = .value answer ∨ middle = .unwind) ∧
      ModeSource operations policy contracts tables families actions world captured input middle firstDemand firstRequirements firstScope ∧
      ModeSource operations policy contracts tables families actions world tail middle output secondDemand secondRequirements secondScope ∧
      scope = firstScope.append secondScope ∧ demand = firstDemand ++ secondDemand ∧
      ∀ store receiving phases,
        evaluate store receiving phases requirements =
          merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) phases firstRequirements)
            (evaluate store receiving (spendAll phases firstDemand) secondRequirements) := by
  rw [handler_cut_reconstructs cut] at source
  obtain ⟨middle, firstDemand, secondDemand, firstRequirements, secondRequirements,
    firstScope, secondScope, first, second, sameScope, sameDemand, evaluation⟩ := source.split
  have selected : HandlerCut requested captured captured .nil handler := by
    clear source first second evaluation
    induction cut with
    | hit handler tail same => exact .hit handler .nil same
    | push frame rest cap tail handler miss next ih => exact .push frame cap cap .nil handler miss ih
    | live ticket q a saved scope rest cap tail handler next ih => exact .live ticket q a saved scope cap cap .nil handler ih
    | spent ticket a scope rest cap tail handler next ih => exact .spent ticket a scope cap cap .nil handler ih
  obtain ⟨answer, residual, declaration, boundary⟩ := first.handler_result selected rfl
  exact ⟨answer, residual, middle, firstDemand, secondDemand, firstRequirements, secondRequirements,
    firstScope, secondScope, declaration, boundary, first, second, sameScope, sameDemand, evaluation⟩

/-- Cleanup starts a normally typed callback over the actual mixed-mode
suffix. Its checked row is taken from the original requirement sequence. -/
theorem ModeSource.start_cleanup
    (source : ModeSource operations policy contracts tables families actions world
      (.push (.armed action) rest) .unwind output demand requirements scope)
    (checked : RecursiveRequirements.Checked entries receiving before requirements row) :
    ∃ latent dependencies callbackRow tailRow nextScope,
    ∃ tailRequirements nextRequirements : Requirements demand,
      scope = .cleanup action.requests dependencies nextScope ∧
      Expression operations policy contracts world action.requests .none Environment.empty
        (.app action.action .unit) .unit []
        (.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent)
        (.sequence .pure (.sequence .pure dependencies)) ∧
      ModeSource operations policy contracts tables families actions world rest .unwind output demand tailRequirements nextScope ∧
      ModeSource operations policy contracts tables families actions world (.push (.unwinding action) rest)
        (.value .unit) output demand nextRequirements (.running nextScope) ∧
      RecursiveRequirements.Checked entries
        (OwnerPhases.ofStack tables (.push (.unwinding action) rest) ++ receiving) before
        (.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent) callbackRow ∧
      RecursiveRequirements.Checked entries receiving before nextRequirements tailRow ∧
      row = callbackRow ++ tailRow := by
  cases source with
  | push head tail => cases head with
      | cleanup callback =>
          obtain ⟨callbackRow, tailRow, callbackCheck, tailCheck, same⟩ :=
            RecursiveRequirements.checked_sequence_parts checked
          obtain ⟨expression, appCheck⟩ := cleanup_application_checked callback
            (by simpa only [Requirements.prepend, List.nil_append] using callbackCheck)
          refine ⟨_, _, callbackRow, tailRow, _, _, _, rfl, expression, tail,
            .push (.unwinding callback) tail, appCheck, ?_, same⟩
          apply RecursiveRequirements.evaluate_sound
          simpa only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
            evaluate_empty, spendAll, merge_empty_left] using RecursiveRequirements.checked_complete tailCheck

/-- Callback Unit return exposes the same rich abandoned source and its
checked requirements; it performs no pending ordinary computation. -/
theorem ModeSource.finish_cleanup
    (source : ModeSource operations policy contracts tables families actions world
      (.push (.unwinding action) rest) (.value .unit) output demand requirements scope)
    (checked : RecursiveRequirements.Checked entries receiving before requirements row) :
    ∃ nextScope, ∃ nextRequirements : Requirements demand,
      scope = .running nextScope ∧
      ModeSource operations policy contracts tables families actions world rest .unwind output demand nextRequirements nextScope ∧
      RecursiveRequirements.Checked entries receiving before nextRequirements row := by
  cases source with
  | push head tail => cases head with
      | ordinary frame => cases frame
      | unwinding callback =>
          refine ⟨_, _, rfl, tail, RecursiveRequirements.evaluate_sound ?_⟩
          simpa only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
            evaluate_empty, spendAll, merge_empty_left] using RecursiveRequirements.checked_complete checked

theorem mode_focus_source
    (current : Expression operations policy contracts world allowed runtimeScope Environment.empty
      whole input currentDemand currentRequirements dependencies)
    (pending : ModeSource operations policy contracts tables families actions world
      stack (.value input) output pendingDemand pendingRequirements dependencyScope)
    (scopeTyped : ScopedPorts.EffectScope contracts.erase.ports runtimeScope ticket)
    (position : Focus whole child context) :
    ∃ (plain : PlainData) (nextInput : Value) (childDemand restDemand : List Nat),
    ∃ childRequirements : Requirements childDemand,
    ∃ nextRequirements : Requirements (restDemand ++ pendingDemand),
    ∃ childDependencies restDependencies,
      plain.context = context ∧ plain.scope = runtimeScope ∧
      Expression operations policy contracts world allowed runtimeScope Environment.empty
        child nextInput childDemand childRequirements childDependencies ∧
      ModeSource operations policy contracts tables families actions world
        (.push (.plain plain) stack) (.value nextInput) output (restDemand ++ pendingDemand)
        nextRequirements (.plain restDependencies dependencyScope) ∧
      currentDemand = childDemand ++ restDemand ∧
      FocusDependencies dependencies childDependencies restDependencies ∧
      RequirementPath childRequirements currentRequirements [] ∧
      (∀ entries receiving before,
        RecursiveRequirements.evaluate entries receiving before
          (.sequence (childRequirements.prepend (OwnerPhases.ofStack tables (.push (.plain plain) stack))) nextRequirements) =
        RecursiveRequirements.evaluate entries receiving before
          (.sequence (currentRequirements.prepend (OwnerPhases.ofStack tables stack)) pendingRequirements)) ∧
      LexicalUnwind.UseTransition (.eval ⟨whole, runtimeScope, stack⟩)
        (.eval ⟨child, runtimeScope, .push (.plain plain) stack⟩) [] [] := by
  obtain ⟨nextInput, childDemand, restDemand, childReq, restReq, childDep, restDep,
    childSource, sourceContext, sameDemand, shape, path, evaluation⟩ := rich_focus_decompose current position
  obtain ⟨plain, contextSame, scopeSame, inputAnnotation, outputAnnotation⟩ :=
    RecursiveContexts.prepare_plain (DeclaredSources.expression_erase (expression_erase current))
      position scopeTyped nextInput.erase
  have frame : Frame operations policy contracts tables families world (.plain plain)
      nextInput input restDemand restReq (.plain restDep) allowed allowed :=
    .plain (by simpa only [contextSame, scopeSame] using sourceContext)
      (by simpa only [scopeSame] using scopeTyped) inputAnnotation outputAnnotation
  refine ⟨plain, nextInput, childDemand, restDemand, childReq, _, childDep, restDep,
    contextSame, scopeSame, childSource, .push (.ordinary frame) pending, sameDemand, shape, path, ?_, ?_⟩
  · intro entries receiving before
    simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
      evaluation, sameDemand, PhaseRechecking.spendAll_append, RecursiveContexts.plain_context,
      List.cons_append, RecursiveContexts.evaluate_plain, merge_assoc]
  · apply LexicalUnwind.UseTransition.evaluate
    · simpa only [scopeSame] using RawStep.focus plain (by simpa only [contextSame] using position) stack
    · cases position <;> first | assumption | trivial

/-- A returned value restores the source scope stored in the actual waiting
    frame. Latent annotations survive the value transport and context plug. -/
theorem mode_plug_source
    (current : Expression operations policy contracts world allowed runtimeScope Environment.empty
      value input currentDemand currentRequirements dependencies)
    (pending : ModeSource operations policy contracts tables families actions world
      (.push (.plain plain) tail) (.value input) output pendingDemand pendingRequirements dependencyScope)
    (closed : ClosedValue value) :
    ∃ (nextInput : Value) (frameDemand tailDemand : List Nat),
    ∃ nextRequirements : Requirements frameDemand, ∃ tailRequirements : Requirements tailDemand,
    ∃ nextDependencies restDependencies restScope boundary,
      dependencyScope = .plain restDependencies restScope ∧
      currentDemand = [] ∧ pendingDemand = frameDemand ++ tailDemand ∧
      Expression operations policy contracts world boundary plain.scope Environment.empty
        (plain.context.plug value) nextInput frameDemand nextRequirements nextDependencies ∧
      ModeSource operations policy contracts tables families actions world
        tail (.value nextInput) output tailDemand tailRequirements restScope ∧
      FocusDependencies nextDependencies .pure restDependencies ∧
      (∀ entries receiving before,
        RecursiveRequirements.evaluate entries receiving before
          (.sequence (nextRequirements.prepend (OwnerPhases.ofStack tables tail)) tailRequirements) =
        RecursiveRequirements.evaluate entries receiving before
          (.sequence (currentRequirements.prepend (OwnerPhases.ofStack tables (.push (.plain plain) tail))) pendingRequirements)) ∧
      LexicalUnwind.UseTransition (.eval ⟨value, runtimeScope, .push (.plain plain) tail⟩)
        (.eval ⟨plain.context.plug value, plain.scope, tail⟩) [] [] := by
  have empty := SourceTemplates.expression_value_demand
    (DeclaredSources.expression_erase (expression_erase current)) closed.1
  cases pending with
  | push frame rest => cases frame with
    | ordinary frame => cases frame with
      | plain context scope inputAnnotation outputAnnotation =>
          obtain ⟨combined, nextDependencies, source, shape, evaluation⟩ :=
            rich_context_plug context (Values.change_context (Values.summary current closed.1) closed.1 _ plain.scope)
          refine ⟨_, _, _, combined, _, nextDependencies, _, _, _, rfl, empty, rfl, source, rest, shape, ?_, ?_⟩
          · intro entries receiving before
            simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
              evaluation, RecursiveRecomposition.evaluate_empty,
              RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase (expression_erase current)) closed.1,
              empty, OwnerPhaseTransitions.spendAll,
              RecursiveRecomposition.merge_empty_left, List.nil_append]
          · apply LexicalUnwind.UseTransition.evaluate
            · exact .plug plain value closed runtimeScope tail
            · cases value <;> first | trivial | cases closed.1



end Ash.OneShot.SourceDependencyFrames
#print axioms Ash.OneShot.SourceDependencyFrames.ModeSourceFrame.realizes
#print axioms Ash.OneShot.SourceDependencyFrames.ModeSource.realizes
#print axioms Ash.OneShot.SourceDependencyFrames.Segment.mode_source
#print axioms Ash.OneShot.SourceDependencyFrames.ModeSource.append

#print axioms Ash.OneShot.SourceDependencyFrames.UnwindSource.mode_source
#print axioms Ash.OneShot.SourceDependencyFrames.ModeSource.return_mode

#print axioms Ash.OneShot.SourceDependencyFrames.ModeSource.split
#print axioms Ash.OneShot.SourceDependencyFrames.ModeSource.handler_cut

#print axioms Ash.OneShot.SourceDependencyFrames.cleanup_application_checked
#print axioms Ash.OneShot.SourceDependencyFrames.ModeSource.start_cleanup
#print axioms Ash.OneShot.SourceDependencyFrames.ModeSource.finish_cleanup

#print axioms Ash.OneShot.SourceDependencyFrames.ModeSource.handler_result

#print axioms Ash.OneShot.SourceDependencyFrames.mode_focus_source
#print axioms Ash.OneShot.SourceDependencyFrames.mode_plug_source



namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations
open RecursiveRequirements (Requirements Checked evaluate)
open OwnerPhaseTransitions (spendAll)
open RecursiveRecomposition (evaluate_empty merge_empty_left)

/-- Administrative unwinding preserves the rich mixed suffix and its checked
requirements at the exact successor scope and discharged-owner phases. -/
theorem ModeSource.advance_checked
    (source : ModeSource operations policy contracts tables families actions world stack .unwind output demand requirements scope)
    (step : LexicalUnwind.Advance stack after discharged)
    (checked : Checked entries receiving before requirements row) :
    ∃ nextDemand, ∃ nextRequirements : Requirements nextDemand,
      ModeSource operations policy contracts tables families actions world after .unwind output
        nextDemand nextRequirements scope.afterUnwind ∧
      Checked entries receiving (spendAll before (discharged.filterMap Syntax.ticketProjection)) nextRequirements row := by
  cases step with
  | plain => cases source with | push head tail => cases head with
      | skipped =>
          refine ⟨_, _, tail, RecursiveRequirements.evaluate_sound ?_⟩
          simpa only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
            evaluate_empty, spendAll, merge_empty_left, List.filterMap_nil] using RecursiveRequirements.checked_complete checked
  | handler => cases source with | push head tail => cases head with
      | handler declaration =>
          refine ⟨_, _, tail, RecursiveRequirements.evaluate_sound ?_⟩
          simpa only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
            evaluate_empty, spendAll, merge_empty_left, List.filterMap_nil] using RecursiveRequirements.checked_complete checked
  | cell => cases source with | push head tail => cases head with
      | cell =>
          refine ⟨_, _, tail, RecursiveRequirements.evaluate_sound ?_⟩
          simpa only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
            evaluate_empty, spendAll, merge_empty_left, List.filterMap_cons, List.filterMap_nil, Syntax.ticketProjection] using
            RecursiveRequirements.checked_complete checked
  | spent => cases source with
      | skippedSpent tail =>
          obtain ⟨firstRow, secondRow, first, second, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
          have firstEmpty : firstRow = [] := by
            have evaluated := RecursiveRequirements.checked_complete first
            rw [RecursiveRecomposition.evaluate_spent] at evaluated
            split at evaluated
            · exact (Option.some.inj evaluated).symm
            · cases evaluated
          subst firstRow
          exact ⟨_, _, tail, second⟩
  | retire => cases source with | push head tail => cases head with
      | retiring =>
          obtain ⟨firstRow, secondRow, first, second, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
          have firstEmpty : firstRow = [] := by
            have evaluated := RecursiveRequirements.checked_complete first
            rw [RecursiveRequirements.evaluate_prepend, RecursiveClosing.evaluate_retire] at evaluated
            split at evaluated
            · exact (Option.some.inj evaluated).symm
            · cases evaluated
          subst firstRow
          exact ⟨_, _, tail, second⟩
  | live => cases source with
      | opening saved tail =>
          obtain ⟨combined, result, evaluation⟩ := saved.append (ModeSource.push .retiring tail)
          refine ⟨_, combined, result, RecursiveRequirements.evaluate_sound ?_⟩
          rw [evaluation]
          simpa only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
            RecursiveClosing.evaluate_retire, List.filterMap_nil, spendAll] using RecursiveRequirements.checked_complete checked

/-- The actual closing delimiter ends abandonment and supplies Unit to its
ordinary caller. The caller's rich requirements and annotations are retained. -/
theorem ModeSource.finish_close
    (source : ModeSource operations policy contracts tables families actions world
      (.push (.closing identity caller) rest) .unwind output demand requirements scope)
    (checked : Checked entries receiving before requirements row) :
    ∃ nextScope, ∃ nextRequirements : Requirements demand,
      scope = .running nextScope ∧
      ScopedPorts.EffectScopeKnown contracts.erase.ports caller ∧
      ModeSource operations policy contracts tables families actions world rest (.value .unit) output demand nextRequirements nextScope ∧
      Checked entries receiving before nextRequirements row := by
  cases source with | push head tail => cases head with
    | closing scopeKnown =>
        refine ⟨_, _, rfl, scopeKnown, tail, RecursiveRequirements.evaluate_sound ?_⟩
        simpa only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
          evaluate_empty, spendAll, merge_empty_left] using RecursiveRequirements.checked_complete checked
end Ash.OneShot.SourceDependencyFrames
#print axioms Ash.OneShot.SourceDependencyFrames.ModeSource.advance_checked
#print axioms Ash.OneShot.SourceDependencyFrames.ModeSource.finish_close


namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations
open RecursiveRequirements (Requirements Checked)
open OwnerPhaseTransitions (available spendAll)

/-- The existing unwind-prefix check determines which source frames will be
skipped and which callbacks must run. No cleanup source is inferred afresh from
runtime code, and retirement markers remain admissible. -/
theorem ModeSource.unwind_source
    (source : ModeSource operations policy contracts tables families actions world stack input output demand requirements scope)
    (scopes : LexicalUnwind.UnwindPrefix stack) :
    ∃ closeDemand, ∃ closeRequirements : Requirements closeDemand,
      UnwindSource operations policy contracts tables families world stack closeDemand closeRequirements scope := by
  induction scopes generalizing input output demand requirements scope with
  | nil => cases source; exact ⟨_, _, .nil⟩
  | plain next ih => cases source with | push head tail => cases head with
      | ordinary frame => cases frame with
          | plain context caller inputAnnotation outputAnnotation =>
              obtain ⟨closeDemand, closeRequirements, source⟩ := ih tail
              exact ⟨_, _, .plain source⟩
      | skipped =>
          obtain ⟨closeDemand, closeRequirements, source⟩ := ih tail
          exact ⟨_, _, .plain source⟩
  | handler next ih => cases source with | push head tail => cases head with
      | ordinary frame => cases frame with
          | handler caller annotation clauses coverage unique declarations capabilities modes =>
              obtain ⟨closeDemand, closeRequirements, source⟩ := ih tail
              exact ⟨_, _, .handler (.handler caller annotation clauses coverage unique declarations capabilities modes) source⟩
      | handler frame =>
          obtain ⟨closeDemand, closeRequirements, source⟩ := ih tail
          exact ⟨_, _, .handler frame source⟩
  | cell next ih => cases source with | push head tail => cases head with
      | ordinary frame => cases frame with
          | cell caller excluded annotation interface =>
              obtain ⟨closeDemand, closeRequirements, source⟩ := ih tail
              exact ⟨_, _, .cell source⟩
      | cell =>
          obtain ⟨closeDemand, closeRequirements, source⟩ := ih tail
          exact ⟨_, _, .cell source⟩
  | armed next ih => cases source with | push head tail => cases head with
      | ordinary frame => cases frame with
          | armed caller callback annotation interface =>
              obtain ⟨closeDemand, closeRequirements, source⟩ := ih tail
              exact ⟨_, _, .cleanup callback source⟩
      | cleanup callback =>
          obtain ⟨closeDemand, closeRequirements, source⟩ := ih tail
          exact ⟨_, _, .cleanup callback source⟩
  | retiring next ih => cases source with | push head tail => cases head with
      | ordinary frame => cases frame with
          | retiring known interface =>
              obtain ⟨closeDemand, closeRequirements, source⟩ := ih tail
              exact ⟨_, _, .retiring source⟩
      | retiring =>
          obtain ⟨closeDemand, closeRequirements, source⟩ := ih tail
          exact ⟨_, _, .retiring source⟩
  | live inside outside ihInside ihOutside => cases source with
      | live known rights inputAnnotation answerAnnotation caller held saved answer tail =>
          obtain ⟨firstDemand, firstRequirements, first⟩ := ihInside saved
          obtain ⟨secondDemand, secondRequirements, second⟩ := ihOutside tail
          exact ⟨_, _, .live first second⟩
      | opening saved tail =>
          obtain ⟨firstDemand, firstRequirements, first⟩ := ihInside saved
          obtain ⟨secondDemand, secondRequirements, second⟩ := ihOutside tail
          exact ⟨_, _, .live first second⟩
  | spent next ih => cases source with
      | spent known annotation caller tail =>
          obtain ⟨closeDemand, closeRequirements, source⟩ := ih tail
          exact ⟨_, _, .spent source⟩
      | skippedSpent tail =>
          obtain ⟨closeDemand, closeRequirements, source⟩ := ih tail
          exact ⟨_, _, .spent source⟩

/-- Reuse the established ownership theorem for the derived cleanup source.
Switching to cleanup retains exactly the same outstanding owner demand when
the predecessor fragment already accounts for its owned continuations. -/
theorem ModeSource.unwind_reentry
    (source : ModeSource operations policy contracts tables families actions world stack input output demand requirements scope)
    (scopes : LexicalUnwind.UnwindPrefix stack)
    (balance : demand.Perm (ownedTickets stack)) :
    ∃ closeDemand, ∃ closeRequirements : Requirements closeDemand,
      UnwindSource operations policy contracts tables families world stack closeDemand closeRequirements scope ∧
      closeDemand.Perm demand := by
  obtain ⟨closeDemand, closeRequirements, cleanup⟩ := source.unwind_source scopes
  exact ⟨closeDemand, closeRequirements, cleanup, cleanup.template.ownership.trans balance.symm⟩
end Ash.OneShot.SourceDependencyFrames
#print axioms Ash.OneShot.SourceDependencyFrames.ModeSource.unwind_source
#print axioms Ash.OneShot.SourceDependencyFrames.ModeSource.unwind_reentry



namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations
open RecursiveRequirements (Requirements)

/-- The actual captured boundary selects ordinary return or lexical cleanup.
The cleanup case derives its demand balance from predecessor usage evidence;
it does not assume the reentered source or its ownership balance. -/
theorem ModeSource.reentry_from_bounds
    (source : ModeSource operations policy contracts tables families actions world
      front (.value answer) (.value answer) frontDemand frontRequirements frontScope)
    (returns : boundary = .value answer ∨ boundary = .unwind)
    (frontUse : LexicalUnwind.StackUse policy actions front .ordinary .ordinary frontUseDemand)
    (aligned : frontDemand.Perm frontUseDemand)
    (savedUse : LexicalUnwind.StackUse policy actions captured .ordinary boundary.mode captureDemand)
    (tailUse : LexicalUnwind.StackUse policy actions tail boundary.mode finalMode tailDemand)
    (bounds : LexicalUnwind.ReentryBounds front captured tail boundary.mode)
    (balance : (frontUseDemand ++ captureDemand ++ tailDemand).Perm
      (ownedTickets front ++ ownedTickets captured ++ ownedTickets tail))
    (unique : (ownedTickets front ++ ownedTickets captured ++ ownedTickets tail).Nodup) :
    ∃ restoredDemand, ∃ restoredRequirements : Requirements restoredDemand,
      ModeSource operations policy contracts tables families actions world front boundary boundary
        restoredDemand restoredRequirements frontScope ∧ restoredDemand.Perm frontDemand := by
  rcases returns with rfl | rfl
  · exact ⟨frontDemand, frontRequirements, source, .refl _⟩
  · have balanced := LexicalUnwind.reentry_unwind_balance frontUse savedUse tailUse bounds balance unique
    cases bounds with
    | unwind scopes inside saved outside =>
        obtain ⟨demand, requirements, cleanup, same⟩ := source.unwind_reentry scopes (aligned.trans balanced)
        obtain ⟨normalized, restored, _⟩ := cleanup.mode_source (actions := actions)
        exact ⟨demand, normalized, restored, same⟩

/-- Recompose the actual saved continuation, caller fragment and spent owner.
The caller fragment is derived at the captured return mode, including the
unwind case. Requirement checking of its cleanup effects is separate. -/
theorem ModeSource.resume_recomposition
    (known : contracts owner = some contract)
    (answerAnnotation : contract.answer.erase.port = ScopedPorts.eraseType answerType)
    (callerScope : ScopedPorts.EffectScopeKnown contracts.erase.ports caller)
    (saved : ModeSource operations policy contracts tables families actions world
      captured (.value contract.input) boundary captureDemand captureRequirements capturedScope)
    (frontSource : ModeSource operations policy contracts tables families actions world
      front (.value contract.answer) (.value contract.answer) frontDemand frontRequirements frontScope)
    (tailSource : ModeSource operations policy contracts tables families actions world
      tail boundary output tailDemand tailRequirements tailScope)
    (returns : boundary = .value contract.answer ∨ boundary = .unwind)
    (frontUse : LexicalUnwind.StackUse policy actions front .ordinary .ordinary frontUseDemand)
    (savedUse : LexicalUnwind.StackUse policy actions captured .ordinary boundary.mode captureUseDemand)
    (tailUse : LexicalUnwind.StackUse policy actions tail boundary.mode output.mode tailUseDemand)
    (frontAligned : frontDemand.Perm frontUseDemand)
    (savedAligned : captureDemand.Perm captureUseDemand)
    (tailAligned : tailDemand.Perm tailUseDemand)
    (bounds : LexicalUnwind.ReentryBounds front captured tail boundary.mode)
    (balance : (frontUseDemand ++ captureUseDemand ++ tailUseDemand).Perm
      (ownedTickets front ++ ownedTickets captured ++ ownedTickets tail))
    (unique : (ownedTickets front ++ ownedTickets captured ++ ownedTickets tail).Nodup) :
    ∃ demand, ∃ requirements : Requirements demand,
      ModeSource operations policy contracts tables families actions world
        (captured.append (front.append (.spent owner answerType caller tail)))
        (.value contract.input) output demand requirements
        (capturedScope.append (frontScope.append (.spent owner tailScope))) ∧
      demand.Perm (captureDemand ++ frontDemand ++ tailDemand) ∧
      demand.Perm (ownedTickets (captured.append (front.append (.spent owner answerType caller tail)))) := by
  obtain ⟨restoredDemand, restoredRequirements, restored, same⟩ :=
    frontSource.reentry_from_bounds returns frontUse frontAligned savedUse tailUse bounds balance unique
  have waiting : ∃ next : Requirements tailDemand,
      ModeSource operations policy contracts tables families actions world
        (.spent owner answerType caller tail) boundary output tailDemand next (.spent owner tailScope) := by
    rcases returns with rfl | rfl
    · exact ⟨_, .spent known answerAnnotation callerScope tailSource⟩
    · exact ⟨_, .skippedSpent tailSource⟩
  obtain ⟨waitingRequirements, waiting⟩ := waiting
  obtain ⟨callerRequirements, callerSource, _⟩ := restored.append waiting
  obtain ⟨requirements, result, _⟩ := saved.append callerSource
  have demandSame : (captureDemand ++ (restoredDemand ++ tailDemand)).Perm
      (captureDemand ++ frontDemand ++ tailDemand) := by
    simpa only [List.append_assoc] using (same.append_right tailDemand).append_left captureDemand
  have sourceBalance : (frontDemand ++ captureDemand ++ tailDemand).Perm
      (ownedTickets front ++ ownedTickets captured ++ ownedTickets tail) :=
    ((frontAligned.append savedAligned).append tailAligned).trans balance
  have exchanged : (captureDemand ++ frontDemand ++ tailDemand).Perm
      (ownedTickets captured ++ ownedTickets front ++ ownedTickets tail) :=
    ((List.perm_append_comm (l₁ := captureDemand) (l₂ := frontDemand)).append_right tailDemand).trans
      (sourceBalance.trans ((List.perm_append_comm (l₁ := ownedTickets front)
        (l₂ := ownedTickets captured)).append_right (ownedTickets tail)))
  refine ⟨_, requirements, result, demandSame, ?_⟩
  simpa only [owned_tickets_append, ownedTickets, List.append_assoc] using demandSame.trans exchanged
end Ash.OneShot.SourceDependencyFrames
#print axioms Ash.OneShot.SourceDependencyFrames.ModeSource.reentry_from_bounds
#print axioms Ash.OneShot.SourceDependencyFrames.ModeSource.resume_recomposition



namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations
open RecursiveRequirements (Requirements evaluate)
open OwnerPhaseTransitions (spendAll)
open ProtectionResiduals

/-- Extract the selected live capture from its predecessor source. A demanded
owner cannot be scheduled for implicit retirement in the same unique pending
demand, so the live boundary is ordinary and retains the exact contract types. -/
theorem ModeSource.extract_live
    (source : ModeSource operations policy contracts tables families actions world
      (front.append (.live owner inputType answerType captured caller tail))
      (.value contract.answer) output demand requirements scope)
    (known : contracts owner = some contract)
    (checked : RecursiveRequirements.Checked entries receiving before
      (.sequence (.invoke ⟨owner, .resume⟩ contract.resumeDemand nearer) requirements) row) :
    ∃ (boundary : ModeValue) (frontDemand tailDemand : List Nat),
    ∃ frontRequirements : Requirements frontDemand,
    ∃ capturedRequirements : Requirements contract.resumeDemand,
    ∃ tailRequirements : Requirements tailDemand,
    ∃ frontScope capturedScope tailScope,
      ModeSource operations policy contracts tables families actions world front
        (.value contract.answer) (.value contract.answer) frontDemand frontRequirements frontScope ∧
      ModeSource operations policy contracts tables families actions world captured
        (.value contract.input) boundary contract.resumeDemand capturedRequirements capturedScope ∧
      ModeSource operations policy contracts tables families actions world tail
        boundary output tailDemand tailRequirements tailScope ∧
      (boundary = .value contract.answer ∨ boundary = .unwind) ∧
      contract.input.erase.port = ScopedPorts.eraseType inputType ∧
      contract.answer.erase.port = ScopedPorts.eraseType answerType ∧
      ScopedPorts.EffectScopeKnown contracts.erase.ports caller ∧
      contract.held = ProtectionContexts.protectedMode captured.erase ∧
      scope = frontScope.append (.live owner capturedScope tailScope) ∧
      demand = frontDemand ++ tailDemand ∧
      ∀ store receiving phases,
        evaluate store receiving phases requirements =
          merge (evaluate store (OwnerPhases.ofStack tables (.live owner inputType answerType captured caller tail) ++ receiving)
            phases frontRequirements)
            (evaluate store receiving (spendAll phases frontDemand) (.sequence (.spent owner) tailRequirements)) := by
  have unused : owner ∉ demand := by
    have unique := RecursiveRequirements.checked_once checked
    intro member
    exact (List.nodup_cons.mp unique).1 (List.mem_append_right _ member)
  obtain ⟨middle, frontDemand, restDemand, frontRequirements, restRequirements,
    frontScope, restScope, frontSource, restSource, sameScope, sameDemand, evaluation⟩ := source.split
  cases restSource with
  | live actual rights inputAnnotation answerAnnotation callerScope held saved answer remaining =>
      cases Option.some.inj (known.symm.trans actual)
      exact ⟨_, frontDemand, restDemand, frontRequirements, _, _, frontScope, _, _,
        frontSource, saved, remaining, answer, inputAnnotation, answerAnnotation, callerScope,
        held, sameScope, sameDemand, evaluation⟩
  | opening saved remaining =>
      apply False.elim
      apply unused
      rw [sameDemand]
      simp
end Ash.OneShot.SourceDependencyFrames
#print axioms Ash.OneShot.SourceDependencyFrames.ModeSource.extract_live



namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution
open SourceDependencyAnnotations
/-- Reuse ordinary frame and expression transport for the mixed source. -/
theorem ModeSourceFrame.transport
    (source : ModeSourceFrame operations policy contracts tables families world entry input output demand requirements layer)
    (extension : contracts.Extends nextContracts) (larger : world ⊆ nextWorld) :
    ModeSourceFrame operations policy nextContracts tables families nextWorld entry input output demand requirements layer := by
  have ports := CoherentSourceTypes.Owners.port_contracts_extension (erased_contract_extension extension)
  cases source with
  | ordinary frame => exact .ordinary (frame.transport extension larger)
  | unwinding callback => exact .unwinding (expression_transport callback extension larger)
  | closing scope => exact .closing (ScopedPorts.effect_scope_known_extension scope ports)
  | retiring => exact .retiring
  | skipped => exact .skipped
  | handler frame => exact .handler (frame.transport extension larger)
  | cell => exact .cell
  | cleanup callback => exact .cleanup (expression_transport callback extension larger)

theorem ModeSource.transport
    (source : ModeSource operations policy contracts tables families actions world stack input output demand requirements scope)
    (extension : contracts.Extends nextContracts) (permissions : Syntax.UsageExtension actions nextActions)
    (larger : world ⊆ nextWorld) :
    ModeSource operations policy nextContracts tables families nextActions nextWorld stack input output demand requirements scope := by
  have ports := CoherentSourceTypes.Owners.port_contracts_extension (erased_contract_extension extension)
  induction source with
  | nil => exact .nil
  | push head tail ih => exact .push (head.transport extension larger) ih
  | live known rights inputAnnotation answerAnnotation caller held saved answer tail ihSaved ihTail =>
      exact .live (extension _ _ known) (permissions _ _ rights) inputAnnotation answerAnnotation
        (ScopedPorts.effect_scope_known_extension caller ports) held ihSaved answer ihTail
  | opening saved tail ihSaved ihTail => exact .opening ihSaved ihTail
  | spent known annotation caller tail ih =>
      exact .spent (extension _ _ known) annotation (ScopedPorts.effect_scope_known_extension caller ports) ih
  | skippedSpent tail ih => exact .skippedSpent ih
end Ash.OneShot.SourceDependencyFrames
#print axioms Ash.OneShot.SourceDependencyFrames.ModeSourceFrame.transport
#print axioms Ash.OneShot.SourceDependencyFrames.ModeSource.transport



namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations
open RecursiveRequirements (Requirements Checked Store evaluate)
open OwnerPhaseTransitions (Phases spend spendAll)

/-- Mixed-mode append uses the same finite requirement evaluator as ordinary
append. Each fragment is checked at its actual enclosing stack and phase. -/
theorem ModeSource.append_checked
    (first : ModeSource operations policy contracts tables families actions world
      front input middle firstDemand firstRequirements firstScope)
    (second : ModeSource operations policy contracts tables families actions world
      tail middle output secondDemand secondRequirements secondScope)
    (firstChecked : Checked entries (OwnerPhases.ofStack tables tail ++ receiving) before firstRequirements firstRow)
    (secondChecked : Checked entries receiving (spendAll before firstDemand) secondRequirements secondRow) :
    ∃ combined : Requirements (firstDemand ++ secondDemand),
      ModeSource operations policy contracts tables families actions world (front.append tail)
        input output (firstDemand ++ secondDemand) combined (firstScope.append secondScope) ∧
      Checked entries receiving before combined (firstRow ++ secondRow) := by
  obtain ⟨combined, source, evaluation⟩ := first.append second
  refine ⟨combined, source, RecursiveRequirements.evaluate_sound ?_⟩
  rw [evaluation, RecursiveRequirements.checked_complete firstChecked,
    RecursiveRequirements.checked_complete secondChecked]
  rfl

/-- Finite caller annotation for a continuation's actual return mode. Ordinary
return keeps the current source check. Unwind return checks the caller's lexical
cleanup source at the actual receiving interpretations and owner phase. The
annotation contains no successor machine or quantification over executions. -/
inductive ReturnEffects (operations : Operations) (policy : Syntax.TicketPolicy)
    (contracts : Contracts) (tables : CallableProtectionFrames.Tables) (families : Families)
    (world : List Nat) (front : Stack) (demand : List Nat) (scope : DependencyScope)
    (receiving : OwnerPhases.Context) (before : Phases) (budget : Footprint) : LexicalUnwind.UseMode → Prop where
  | ordinary : ReturnEffects operations policy contracts tables families world front demand scope receiving before budget .ordinary
  | unwind (source : UnwindSource operations policy contracts tables families world front closingDemand closingRequirements scope)
      (aligned : closingDemand.Perm demand)
      (effects : ClosingEffects budget receiving before closingRequirements) :
      ReturnEffects operations policy contracts tables families world front demand scope receiving before budget .unwind

/-- The checked ordinary fragment supplies the retirement trace. Reuse trace
permutation and the structural cleanup-effect proof to derive the reentered
source and its row; no successor check or owner-readiness premise is supplied. -/
theorem ReturnEffects.source_checked
    (annotation : ReturnEffects operations policy contracts tables families world front demand scope receiving before budget boundary.mode)
    (source : ModeSource operations policy contracts tables families actions world front
      (.value answer) (.value answer) demand requirements scope)
    (returns : boundary = .value answer ∨ boundary = .unwind)
    (checked : Checked entries receiving before requirements row)
    (bounded : row ⊆ budget) :
    ∃ nextDemand, ∃ nextRequirements : Requirements nextDemand, ∃ nextRow,
      ModeSource operations policy contracts tables families actions world front
        boundary boundary nextDemand nextRequirements scope ∧
      nextDemand.Perm demand ∧ Checked entries receiving before nextRequirements nextRow ∧ nextRow ⊆ budget := by
  rcases returns with rfl | rfl
  · exact ⟨demand, requirements, row, source, .refl _, checked, bounded⟩
  · cases annotation with
    | unwind cleanup aligned effects =>
        have trace := OwnerPhaseTransitions.trace_permutation
          (RecursiveRequirements.checked_trace checked) aligned.symm
        obtain ⟨nextRow, nextChecked, covered⟩ := effects.checked (store := entries) trace
        obtain ⟨normalized, nextSource, evaluation⟩ := cleanup.mode_source (actions := actions)
        refine ⟨_, normalized, nextRow, nextSource, aligned, RecursiveRequirements.evaluate_sound ?_, covered⟩
        rw [evaluation]
        exact RecursiveRequirements.checked_complete nextChecked

/-- The unwind annotation is checked by the existing finite evaluator on its
retained lexical cleanup source. The predecessor check supplies readiness; the
annotation does not ask for a proof about a future execution. -/
theorem ReturnEffects.unwind_iff
    (checked : Checked entries receiving before (owners := demand) requirements row) :
    ReturnEffects operations policy contracts tables families world front demand scope receiving before budget .unwind ↔
      ∃ closingDemand, ∃ closingRequirements : Requirements closingDemand,
        UnwindSource operations policy contracts tables families world front closingDemand closingRequirements scope ∧
        closingDemand.Perm demand ∧
        ∃ closingRow, evaluate entries receiving before closingRequirements = some closingRow ∧ closingRow ⊆ budget := by
  constructor
  · intro annotation
    cases annotation with
    | unwind source aligned effects =>
        obtain ⟨closingRow, closingCheck, covered⟩ := effects.checked (store := entries)
          (OwnerPhaseTransitions.trace_permutation (RecursiveRequirements.checked_trace checked) aligned.symm)
        exact ⟨_, _, source, aligned, closingRow, RecursiveRequirements.checked_complete closingCheck, covered⟩
  · rintro ⟨closingDemand, closingRequirements, source, aligned, closingRow, evaluated, covered⟩
    exact .unwind source aligned
      (source.template.effects_of_checked (RecursiveRequirements.evaluate_sound evaluated) covered)

/-- Join the saved body, the caller checked for its actual return mode, and
the spent-owner suffix. The complete successor requirement check is a result,
including when caller code is replaced by lexical cleanup. -/
theorem ModeSource.resume_checked_recomposition
    (known : contracts owner = some contract)
    (answerAnnotation : contract.answer.erase.port = ScopedPorts.eraseType answerType)
    (callerScope : ScopedPorts.EffectScopeKnown contracts.erase.ports caller)
    (saved : ModeSource operations policy contracts tables families actions world
      captured (.value contract.input) boundary captureDemand captureRequirements capturedScope)
    (frontSource : ModeSource operations policy contracts tables families actions world
      front (.value contract.answer) (.value contract.answer) frontDemand frontRequirements frontScope)
    (tailSource : ModeSource operations policy contracts tables families actions world
      tail boundary output tailDemand tailRequirements tailScope)
    (returns : boundary = .value contract.answer ∨ boundary = .unwind)
    (consumed : before owner = .consumed)
    (savedChecked : Checked entries
      (OwnerPhases.ofStack tables (front.append (.spent owner answerType caller tail)) ++ receiving)
      before captureRequirements captureRow)
    (frontChecked : Checked entries
      (OwnerPhases.ofStack tables (.spent owner answerType caller tail) ++ receiving)
      (spendAll before captureDemand) frontRequirements frontRow)
    (tailChecked : Checked entries receiving (spendAll (spendAll before captureDemand) frontDemand)
      tailRequirements tailRow)
    (frontBound : frontRow ⊆ budget)
    (callerEffects : ReturnEffects operations policy contracts tables families world front frontDemand frontScope
      (OwnerPhases.ofStack tables (.spent owner answerType caller tail) ++ receiving)
      (spendAll before captureDemand) budget boundary.mode) :
    ∃ demand, ∃ requirements : Requirements demand, ∃ row,
      ModeSource operations policy contracts tables families actions world
        (captured.append (front.append (.spent owner answerType caller tail)))
        (.value contract.input) output demand requirements
        (capturedScope.append (frontScope.append (.spent owner tailScope))) ∧
      demand.Perm (captureDemand ++ frontDemand ++ tailDemand) ∧
      Checked entries receiving before requirements row ∧ row ⊆ captureRow ++ budget ++ tailRow := by
  obtain ⟨restoredDemand, restoredRequirements, restoredRow, restored, same, restoredChecked, covered⟩ :=
    callerEffects.source_checked frontSource returns frontChecked frontBound
  have spentSource : ∃ waiting : Requirements tailDemand,
      ModeSource operations policy contracts tables families actions world
        (.spent owner answerType caller tail) boundary output tailDemand waiting (.spent owner tailScope) ∧
      Checked entries receiving (spendAll (spendAll before captureDemand) restoredDemand) waiting tailRow := by
    have phased : spendAll (spendAll before captureDemand) restoredDemand =
        spendAll (spendAll before captureDemand) frontDemand :=
      PhaseRechecking.spendAll_permutation same
    have stillConsumed : spendAll (spendAll before captureDemand) restoredDemand owner = .consumed :=
      RecursiveTransport.phases_spendAll_later owner (RecursiveTransport.phases_spendAll_later owner consumed)
    have waitingChecked : Checked entries receiving
        (spendAll (spendAll before captureDemand) restoredDemand)
        (.sequence (.spent owner) tailRequirements) tailRow := by
      simpa only [spendAll, List.nil_append] using
        (Checked.sequence (Checked.spent stillConsumed) (phased ▸ tailChecked))
    rcases returns with rfl | rfl
    · exact ⟨_, .spent known answerAnnotation callerScope tailSource, waitingChecked⟩
    · exact ⟨_, .skippedSpent tailSource, waitingChecked⟩
  obtain ⟨waitingRequirements, waitingSource, waitingChecked⟩ := spentSource
  obtain ⟨callerRequirements, callerSource, callerChecked⟩ :=
    restored.append_checked waitingSource restoredChecked waitingChecked
  obtain ⟨requirements, joinedSource, joinedChecked⟩ :=
    saved.append_checked callerSource savedChecked callerChecked
  refine ⟨_, requirements, _, joinedSource, ?_, joinedChecked, ?_⟩
  · simpa only [List.append_assoc] using (same.append_right tailDemand).append_left captureDemand
  · intro item member
    rcases List.mem_append.mp member with first | rest
    · exact List.mem_append_left _ (List.mem_append_left _ first)
    · rcases List.mem_append.mp rest with middle | last
      · exact List.mem_append_left _ (List.mem_append_right _ (covered middle))
      · exact List.mem_append_right _ last

end Ash.OneShot.SourceDependencyFrames
#print axioms Ash.OneShot.SourceDependencyFrames.ModeSource.append_checked
#print axioms Ash.OneShot.SourceDependencyFrames.ReturnEffects.unwind_iff
#print axioms Ash.OneShot.SourceDependencyFrames.ReturnEffects.source_checked
#print axioms Ash.OneShot.SourceDependencyFrames.ModeSource.resume_checked_recomposition





namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations
open RecursiveRequirements (Requirements Checked)
open OwnerPhaseTransitions (spendAll)

/-- For a caller with no remaining continuation demand, existing lexical
source and requirement checks already supply the cleanup path and its effect
bound. Available physical owners rule out an unaccounted dormant live capture.
Normal-only pending code may have arbitrary effects; it is skipped on unwind. -/
theorem ModeSource.unwind_checked_empty
    (source : ModeSource operations policy contracts tables families actions world
      stack input output demand requirements scope)
    (empty : demand = [])
    (scopes : LexicalUnwind.UnwindPrefix stack)
    (checked : Checked entries receiving before requirements row)
    (ready : ∀ owner ∈ ownedTickets stack, before owner = .available) :
    ∃ closingRequirements : Requirements [], ∃ closingRow,
      UnwindSource operations policy contracts tables families world stack [] closingRequirements scope ∧
      Checked entries receiving before closingRequirements closingRow ∧ closingRow ⊆ row := by
  induction scopes generalizing input output demand scope requirements receiving before row with
  | nil => cases source; exact ⟨_, _, .nil, checked, List.Subset.refl _⟩
  | plain next ih => cases source with | push head tail =>
      rcases List.append_eq_nil_iff.mp empty with ⟨rfl, rfl⟩
      obtain ⟨headRow, tailRow, first, last, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
      cases head with
      | ordinary frame => cases frame with
          | plain context caller inputAnnotation outputAnnotation =>
            obtain ⟨closing, closingRow, closed, check, bounded⟩ := ih tail rfl last ready
            exact ⟨_, closingRow, .plain closed, check, bounded.trans (List.subset_append_right _ _)⟩
      | skipped =>
          obtain ⟨closing, closingRow, closed, check, bounded⟩ := ih tail rfl last ready
          exact ⟨_, closingRow, .plain closed, check, bounded.trans (List.subset_append_right _ _)⟩
  | handler next ih => cases source with | push head tail =>
      rcases List.append_eq_nil_iff.mp empty with ⟨rfl, rfl⟩
      obtain ⟨headRow, tailRow, first, last, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
      cases head with
      | ordinary frame => cases frame with
          | handler caller annotation clauses coverage unique declarations capabilities modes =>
            obtain ⟨closing, closingRow, closed, check, bounded⟩ := ih tail rfl last ready
            exact ⟨_, closingRow, .handler (.handler caller annotation clauses coverage unique declarations capabilities modes) closed,
              check, bounded.trans (List.subset_append_right _ _)⟩
      | handler declaration =>
          obtain ⟨closing, closingRow, closed, check, bounded⟩ := ih tail rfl last ready
          exact ⟨_, closingRow, .handler declaration closed, check, bounded.trans (List.subset_append_right _ _)⟩
  | cell next ih => cases source with | push head tail =>
      rcases List.append_eq_nil_iff.mp empty with ⟨rfl, rfl⟩
      obtain ⟨headRow, tailRow, first, last, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
      cases head with
      | ordinary frame => cases frame with
          | cell caller excluded annotation interface =>
            obtain ⟨closing, closingRow, closed, check, bounded⟩ := ih tail rfl last ready
            exact ⟨_, closingRow, .cell closed, check, bounded.trans (List.subset_append_right _ _)⟩
      | cell =>
          obtain ⟨closing, closingRow, closed, check, bounded⟩ := ih tail rfl last ready
          exact ⟨_, closingRow, .cell closed, check, bounded.trans (List.subset_append_right _ _)⟩
  | armed next ih => cases source with | push head tail =>
      rcases List.append_eq_nil_iff.mp empty with ⟨rfl, rfl⟩
      obtain ⟨headRow, tailRow, first, last, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
      cases head with
      | ordinary frame => cases frame with
          | armed caller callback annotation interface =>
            obtain ⟨closing, closingRow, closed, check, bounded⟩ := ih tail rfl last ready
            refine ⟨_, headRow ++ closingRow, .cleanup callback closed, .sequence ?_ check, ?_⟩
            · simpa only [Requirements.prepend, List.nil_append] using first
            · exact List.append_subset.mpr ⟨List.subset_append_left _ _, bounded.trans (List.subset_append_right _ _)⟩
      | cleanup callback =>
          obtain ⟨closing, closingRow, closed, check, bounded⟩ := ih tail rfl last ready
          refine ⟨_, headRow ++ closingRow, .cleanup callback closed, .sequence ?_ check, ?_⟩
          · simpa only [Requirements.prepend, List.nil_append] using first
          · exact List.append_subset.mpr ⟨List.subset_append_left _ _, bounded.trans (List.subset_append_right _ _)⟩
  | retiring next ih => cases source with | push head tail =>
      rcases List.append_eq_nil_iff.mp empty with ⟨rfl, rfl⟩
      cases head with
      | ordinary frame => cases frame
  | live inside outside ihSaved ihTail => cases source with
      | live known rights inputAnnotation answerAnnotation caller held saved answer tail =>
          cases empty
          obtain ⟨headRow, tailRow, first, last, same⟩ := RecursiveRequirements.checked_sequence_parts checked
          have evaluated := RecursiveRequirements.checked_complete first
          rw [RecursiveRecomposition.evaluate_spent, ready _ List.mem_cons_self] at evaluated
          cases evaluated
      | opening saved tail => simp at empty
  | spent next ih => cases source with
      | spent known annotation caller tail =>
          cases empty
          obtain ⟨headRow, tailRow, first, last, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
          obtain ⟨closing, closingRow, closed, check, bounded⟩ := ih tail rfl last ready
          exact ⟨_, headRow ++ closingRow, .spent closed, .sequence first check,
            List.append_subset.mpr ⟨List.subset_append_left _ _, bounded.trans (List.subset_append_right _ _)⟩⟩
      | skippedSpent tail =>
          cases empty
          obtain ⟨headRow, tailRow, first, last, rfl⟩ := RecursiveRequirements.checked_sequence_parts checked
          obtain ⟨closing, closingRow, closed, check, bounded⟩ := ih tail rfl last ready
          exact ⟨_, headRow ++ closingRow, .spent closed, .sequence first check,
            List.append_subset.mpr ⟨List.subset_append_left _ _, bounded.trans (List.subset_append_right _ _)⟩⟩

end Ash.OneShot.SourceDependencyFrames
#print axioms Ash.OneShot.SourceDependencyFrames.ModeSource.unwind_checked_empty

namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations
open RecursiveRequirements (Requirements Checked)
open OwnerPhaseTransitions (spendAll)

/-- No new cleanup annotation is required when the ordinary caller has no
outstanding continuation demand. Typed scope metadata and its current finite
effect check construct the return certificate at either continuation mode. -/
theorem ModeSource.return_effects_of_empty
    (source : ModeSource operations policy contracts tables families actions world
      stack input output demand requirements scope)
    (empty : demand = [])
    (scopes : LexicalUnwind.UnwindPrefix stack)
    (checked : Checked entries receiving before requirements row)
    (ready : ∀ owner ∈ ownedTickets stack, before owner = .available)
    (bounded : row ⊆ budget) :
    ReturnEffects operations policy contracts tables families world stack demand scope receiving before budget mode := by
  cases mode with
  | ordinary => exact .ordinary
  | unwind =>
      obtain ⟨closing, closingRow, source, checked, covered⟩ :=
        source.unwind_checked_empty empty scopes checked ready
      exact .unwind source (empty ▸ List.Perm.refl [])
        (source.template.effects_of_checked checked (covered.trans bounded))

/-- Resumption over a caller whose finite demand is empty derives the
cleanup certificate from predecessor source/effect evidence. No ReturnEffects
premise or independently checked successor is required. -/
theorem ModeSource.resume_checked_recomposition_empty
    (known : contracts owner = some contract)
    (answerAnnotation : contract.answer.erase.port = ScopedPorts.eraseType answerType)
    (callerScope : ScopedPorts.EffectScopeKnown contracts.erase.ports caller)
    (saved : ModeSource operations policy contracts tables families actions world
      captured (.value contract.input) boundary captureDemand captureRequirements capturedScope)
    (frontSource : ModeSource operations policy contracts tables families actions world
      front (.value contract.answer) (.value contract.answer) frontDemand frontRequirements frontScope)
    (tailSource : ModeSource operations policy contracts tables families actions world
      tail boundary output tailDemand tailRequirements tailScope)
    (returns : boundary = .value contract.answer ∨ boundary = .unwind)
    (consumed : before owner = .consumed)
    (savedChecked : Checked entries
      (OwnerPhases.ofStack tables (front.append (.spent owner answerType caller tail)) ++ receiving)
      before captureRequirements captureRow)
    (frontChecked : Checked entries
      (OwnerPhases.ofStack tables (.spent owner answerType caller tail) ++ receiving)
      (spendAll before captureDemand) frontRequirements frontRow)
    (tailChecked : Checked entries receiving (spendAll (spendAll before captureDemand) frontDemand)
      tailRequirements tailRow)
    (empty : frontDemand = [])
    (scopes : LexicalUnwind.UnwindPrefix front)
    (ready : ∀ other ∈ ownedTickets front, spendAll before captureDemand other = .available) :
    ∃ demand, ∃ requirements : Requirements demand, ∃ row,
      ModeSource operations policy contracts tables families actions world
        (captured.append (front.append (.spent owner answerType caller tail)))
        (.value contract.input) output demand requirements
        (capturedScope.append (frontScope.append (.spent owner tailScope))) ∧
      demand.Perm (captureDemand ++ frontDemand ++ tailDemand) ∧
      Checked entries receiving before requirements row ∧ row ⊆ captureRow ++ frontRow ++ tailRow := by
  exact ModeSource.resume_checked_recomposition known answerAnnotation callerScope saved frontSource tailSource
    returns consumed savedChecked frontChecked tailChecked (List.Subset.refl _)
    (frontSource.return_effects_of_empty empty scopes frontChecked ready (List.Subset.refl _))

end Ash.OneShot.SourceDependencyFrames
#print axioms Ash.OneShot.SourceDependencyFrames.ModeSource.return_effects_of_empty
#print axioms Ash.OneShot.SourceDependencyFrames.ModeSource.resume_checked_recomposition_empty


namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution
open SourceDependencyAnnotations

def ModeValue.row_boundary : ModeValue → Option CoherentSourceTypes.Value
  | .value result => some result.erase
  | .unwind => none

/-- Erase rich dependencies without changing a frame's requirement tree or
its value/unwind boundary. Callback typing is reused from the stored witness. -/
theorem ModeSourceFrame.row_source
    (source : ModeSourceFrame operations policy contracts tables families world entry input output demand requirements layer) :
    ClauseRowAdmission.StoreModeFrame operations.erase policy contracts.erase world entry
      input.row_boundary output.row_boundary demand requirements := by
  cases source with
  | ordinary frame => exact .ordinary (.ordinary (DeclaredSourceFrames.frame_erase frame.erase.source))
  | unwinding callback => exact .unwinding (DeclaredSourceValues.erase (value_erase callback))
  | closing scope => exact .closing (ScopedPorts.effect_scope_known_has_types scope)
  | retiring => exact .retiring
  | skipped => exact .skipped
  | handler frame => exact .handler (.ordinary (DeclaredSourceFrames.frame_erase frame.erase.source))
  | cell => exact .cell
  | cleanup callback => exact .cleanup (DeclaredSourceValues.erase (value_erase callback))

/-- The actual mixed source authenticates clause-row admission independently
of resume-record collection. No ordinary-only substitute stack is constructed. -/
theorem ModeSource.row_source
    (source : ModeSource operations policy contracts tables families actions world
      stack input output demand requirements dependencyScope) :
    ClauseRowAdmission.StoreModeSource operations.erase policy contracts.erase tables world
      stack input.row_boundary output.row_boundary demand requirements := by
  induction source with
  | nil => exact .nil
  | push head tail ih => exact .push head.row_source ih
  | live known rights inputAnnotation answerAnnotation caller held saved answer tail ihSaved ihTail =>
      refine .live (contract_erase_known known) inputAnnotation answerAnnotation
        (ScopedPorts.effect_scope_known_has_types caller) held ihSaved ?_ ihTail
      rcases answer with rfl | rfl
      · exact .inl rfl
      · exact .inr rfl
  | opening saved tail ihSaved ihTail => exact .opening ihSaved ihTail
  | spent known annotation caller tail ih =>
      exact .spent (contract_erase_known known) annotation (ScopedPorts.effect_scope_known_has_types caller) ih
  | skippedSpent tail ih => exact .skippedSpent ih

end Ash.OneShot.SourceDependencyFrames
#print axioms Ash.OneShot.SourceDependencyFrames.ModeSourceFrame.row_source
#print axioms Ash.OneShot.SourceDependencyFrames.ModeSource.row_source

namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations
open RecursiveRequirements (Requirements Checked)

/-- The existing alternative requirement rule checks the normal and lexical
cleanup paths at the same interface and phase. Its shared owner demand is
consumed by either path, never twice. The resulting bound supplies both return
modes, including callers with outstanding continuations. -/
theorem UnwindSource.choice_return_effects
    (cleanup : UnwindSource operations policy contracts tables families world
      stack closeDemand closeRequirements scope)
    (aligned : demand.Perm closeDemand)
    (checked : Checked entries receiving before
      (.choice (normal : Requirements demand) closeRequirements aligned) row)
    (bounded : row ⊆ budget) :
    (∃ normalRow, Checked entries receiving before normal normalRow ∧ normalRow ⊆ budget) ∧
    (∀ mode, ReturnEffects operations policy contracts tables families world
      stack demand scope receiving before budget mode) := by
  cases checked with
  | choice first second =>
      refine ⟨⟨_, first, (List.subset_append_left _ _).trans bounded⟩, ?_⟩
      intro mode
      cases mode with
      | ordinary => exact .ordinary
      | unwind =>
          exact .unwind cleanup aligned.symm
            (cleanup.template.effects_of_checked second ((List.subset_append_right _ _).trans bounded))

/-- Structural source and owner balance construct the alternative cleanup
annotation. Admission then uses a single existing finite requirement check;
there is no precondition about a future machine or a separately supplied
ReturnEffects certificate. This is local admission at a caller boundary. -/
theorem ModeSource.return_choice_admission
    (source : ModeSource operations policy contracts tables families actions world
      stack input output demand normal scope)
    (scopes : LexicalUnwind.UnwindPrefix stack)
    (balance : demand.Perm (ownedTickets stack)) :
    ∃ closeDemand, ∃ closeRequirements : Requirements closeDemand,
    ∃ aligned : demand.Perm closeDemand,
      UnwindSource operations policy contracts tables families world
        stack closeDemand closeRequirements scope ∧
      ∀ entries receiving before row budget,
        Checked entries receiving before (.choice normal closeRequirements aligned) row →
        row ⊆ budget →
        (∃ normalRow, Checked entries receiving before normal normalRow ∧ normalRow ⊆ budget) ∧
        (∀ mode, ReturnEffects operations policy contracts tables families world
          stack demand scope receiving before budget mode) := by
  obtain ⟨closeDemand, closeRequirements, cleanup, same⟩ := source.unwind_reentry scopes balance
  exact ⟨closeDemand, closeRequirements, same.symm, cleanup,
    fun _ _ _ _ _ checked bounded => cleanup.choice_return_effects same.symm checked bounded⟩

end Ash.OneShot.SourceDependencyFrames
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindSource.choice_return_effects
#print axioms Ash.OneShot.SourceDependencyFrames.ModeSource.return_choice_admission


namespace Ash.OneShot.SourceDependencyFrames
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations
open RecursiveRequirements (Requirements Checked)
open OwnerPhaseTransitions (spendAll)

/-- A static clause certificate supplies a caller's return obligation at a
structural normal/cleanup alternative, after precisely the preceding owners
have been consumed. The exact lexical cleanup source authenticates the branch;
an unrelated extra alternative cannot discharge this rule. -/
theorem UnwindSource.clause_return_effects
    (cleanup : UnwindSource operations policy contracts tables families world
      stack closeDemand closeRequirements scope)
    (aligned : demand.Perm closeDemand)
    (position : RequirementPath (.choice (normal : Requirements demand) closeRequirements aligned)
      annotated prior)
    (rows : ClauseRowAdmission.Rows header annotated templates)
    (authenticated : templates entries)
    (interface : ClauseRowAdmission.Interface header.owner header.contract header.disposes entries
      receiving before requestRow)
    (exported : OwnerSource.exportAt receiving before header.advertised = some requestRow) :
    (∃ normalRow,
      Checked entries (.live header.owner header.contract.held :: receiving)
        (spendAll before prior) normal normalRow ∧
      normalRow ⊆ requestRow ++ header.contract.resumeRow) ∧
    (∀ mode, ReturnEffects operations policy contracts tables families world
      stack demand scope (.live header.owner header.contract.held :: receiving)
      (spendAll before prior) (requestRow ++ header.contract.resumeRow) mode) := by
  obtain ⟨row, checked, covered⟩ := rows.instantiate interface exported authenticated
  obtain ⟨alternativesRow, alternativesCheck, within⟩ := position.checked checked
  exact cleanup.choice_return_effects aligned alternativesCheck (within.trans covered)

end Ash.OneShot.SourceDependencyFrames
#print axioms Ash.OneShot.SourceDependencyFrames.UnwindSource.clause_return_effects
