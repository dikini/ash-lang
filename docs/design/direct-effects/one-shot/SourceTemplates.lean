import CallableSources

/-!
Structural derivation of recursive requirements from shared expression and stack
annotations. Invocation rows come from referenced templates, not cached record
rows. This module establishes template provenance and ordinary ports; preserved
whole-program admission remains a separate obligation.
-/

namespace Ash.OneShot.SourceTemplates
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals CoherentSourceTypes
open RecursiveRequirements (Requirements Key Store)
open Owners (Contracts)

/-- Table modes cover the actions of the corresponding clause, independently
    of its port type and outward effect rows. Both branch arms count. -/
inductive ClauseModes : Clauses → List (Nat × ClauseContract) → Prop where
  | nil : ClauseModes .nil []
  | cons (dispose : body.requiredActions.dispose = true → contract.dispose = true)
      (rest : ClauseModes clauses table) :
      ClauseModes (.cons operation parameter binder body clauses) ((operation, contract) :: table)

theorem clause_modes_substitution (source : ClauseModes clauses table)
    (value : replacement.IsValue) (name : Nat) :
    ClauseModes (clauses.subst name replacement) table := by
  induction source with
  | nil => exact .nil
  | cons dispose rest ih =>
      simp only [Clauses.subst]
      split
      · exact .cons dispose ih
      · exact .cons (by simpa only [Code.substitution_required_actions _ name value] using dispose) ih

theorem clause_modes_instantiation (source : ClauseModes clauses table)
    (environment : Instantiation.Environment) :
    ClauseModes (clauses.instantiate environment) table := by
  induction source with
  | nil => exact .nil
  | cons dispose rest ih =>
      exact .cons (by simpa only [Code.instantiation_required_actions] using dispose) ih

theorem selected_clause_mode (selected : ClauseAt operation clauses parameter binder body)
    (source : ClauseModes clauses table) :
    ∃ contract, lookup operation table = some contract ∧
      (body.requiredActions.dispose = true → contract.dispose = true) := by
  induction selected generalizing table with
  | hit => cases source with
    | cons dispose rest => exact ⟨_, by simp [lookup], dispose⟩
  | pass different next ih => cases source with
    | cons dispose rest =>
      obtain ⟨contract, known, bound⟩ := ih rest
      exact ⟨contract, by simpa only [lookup, if_neg different] using known, bound⟩

inductive Expression (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts) :
    List Nat → List Instance → Execution.Scope → Environment → Code → Value →
      (demand : List Nat) → Requirements demand → Prop where
  | stable (summary : Summary operations world environment allowed code result raw) :
      Expression operations policy contracts world allowed scope environment code result [] (.request [] raw)
  | callable (summary : CallableSources.Summary operations
        (fun world environment requests code value demand requirements =>
          Expression operations policy contracts world requests .none environment code value demand requirements)
        world environment allowed code result raw) :
      Expression operations policy contracts world allowed scope environment code result [] (.request [] raw)
  | lambda (body : Expression operations policy contracts world requests .none
        (environment.extend parameter input) code output bodyDemand bodyRequirements)
      (outward : RecursiveOutward.Outward bodyRequirements (some latent))
      (formed : ScopedPorts.InWorld world (Value.function input output requests latent).port) :
      Expression operations policy contracts world allowed scope environment (.lambda parameter code)
        (.function input output requests latent) [] (.request [] [])
  | purePair (left : Expression operations policy contracts world allowed scope environment a first [] (.request [] []))
      (right : Expression operations policy contracts world allowed scope environment b second [] (.request [] [])) :
      Expression operations policy contracts world allowed scope environment (.pair a b) (.pair first second) [] (.request [] [])
  | pair (leftSource : Expression operations policy contracts world allowed scope environment a first leftDemand left)
      (rightSource : Expression operations policy contracts world allowed scope environment b second rightDemand right) :
      Expression operations policy contracts world allowed scope environment (.pair a b) (.pair first second)
        (leftDemand ++ rightDemand) (.sequence left right)
  | app (functionSource : Expression operations policy contracts world allowed scope environment f
        (.function input output requests latent) functionDemand function)
      (argumentSource : Expression operations policy contracts world allowed scope environment a input argumentDemand argument)
      (admitted : requests ⊆ allowed) :
      Expression operations policy contracts world allowed scope environment (.app f a) output
        (functionDemand ++ argumentDemand) (.emitAfter (.sequence function argument) [] latent)
  | bind (initializerSource : Expression operations policy contracts world allowed scope environment a input initializerDemand initializer)
      (bodySource : Expression operations policy contracts world allowed scope (environment.extend parameter input) b output bodyDemand body) :
      Expression operations policy contracts world allowed scope environment (.bind parameter a b) output
        (initializerDemand ++ bodyDemand) (.sequence initializer body)
  | branch (conditionSource : Expression operations policy contracts world allowed scope environment test .boolean conditionDemand condition)
      (yesSource : Expression operations policy contracts world allowed scope environment a output yesDemand yes)
      (noSource : Expression operations policy contracts world allowed scope environment b output noDemand no)
      (same : yesDemand.Perm noDemand) :
      Expression operations policy contracts world allowed scope environment (.branch test a b) output
        (conditionDemand ++ yesDemand) (.sequence condition (.choice yes no same))
  | perform (known : operations effect operation = some (input, output)) (admitted : effect ∈ allowed)
      (operandSource : Expression operations policy contracts world allowed scope environment value input operandDemand operand)
      (formed : ScopedPorts.InWorld world output.port) :
      Expression operations policy contracts world allowed scope environment (.perform (Instantiation.freezeEffect effect) operation value)
        output operandDemand (.emitAfter operand [] [⟨effect, operation, false⟩])
  | handler (body : Expression operations policy contracts world (effect :: residual) scope environment
        code answer demand requirements)
      (clauses : ScopedPorts.ClausesTyped operations.ports world environment.ports effect answer.port residual arms)
      (capabilities : ClausesUse policy arms)
      (coverage : ScopedPorts.Covers operations.ports effect arms)
      (unique : (ScopedTyping.clauseKeys arms).Nodup) (admitted : residual ⊆ allowed)
      (table : List (Nat × ClauseContract)) (modes : ClauseModes arms table) :
      Expression operations policy contracts world allowed scope environment
        (.handle (Instantiation.freezeEffect effect) code arms) answer demand
        (requirements.prepend [.ordinary (.handler effect 0 table)])
  | resume (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
      (permission : (policy binder).resume = true)
      (operandSource : Expression operations policy contracts world allowed scope environment value contract.input operandDemand operand)
      (admitted : contract.resumeEffects ⊆ allowed) (formed : ScopedPorts.InWorld world contract.answer.port) :
      Expression operations policy contracts world allowed scope environment (.resume binder value) contract.answer
        (operandDemand ++ owner :: contract.resumeDemand) (.sequence operand (.invoke ⟨owner, .resume⟩ contract.resumeDemand []))
  | discard (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
      (permission : (policy binder).dispose = true) (unprotected : contract.held = false)
      (admitted : contract.closeEffects ⊆ allowed) :
      Expression operations policy contracts world allowed scope environment (.discard binder) .unit
        (owner :: contract.closeDemand) (.invoke ⟨owner, .dispose⟩ contract.closeDemand [])
  | cleanup (callbackSource : Expression operations policy contracts world allowed scope environment action
        (.function .unit .unit requests latent) callbackDemand callback)
      (bodySource : Expression operations policy contracts world allowed scope environment code output bodyDemand body)
      (admitted : requests ⊆ allowed) :
      Expression operations policy contracts world allowed scope environment (.cleanup action code) output
        (callbackDemand ++ bodyDemand) (.emitAfter (.sequence callback body) [] (qualify true latent))
  | resource {bodyRow : Nat → Footprint}
      (initializer : Expression operations policy contracts world allowed scope environment initial .integer demand requirements)
      (body : ∀ identity, identity ∉ world → CallableSources.Summary operations
        (fun world environment requests code value demand requirements =>
          Expression operations policy contracts world requests .none environment code value demand requirements)
        (world ++ [identity]) environment (.cell identity :: residual)
        (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output (bodyRow identity))
      (formed : ScopedPorts.InWorld world output.port)
      (effectsBound : residual.flatMap Instance.resources ⊆ world) (admitted : residual ⊆ allowed)
      (outward : ∀ identity, identity ∉ world → CallableProtection.outsideCell identity (bodyRow identity) = raw) :
      Expression operations policy contracts world allowed scope environment (.resource binder initial code)
        output demand (.emitAfter requirements [] raw)
  | scopedResource {bodyRequirements : Nat → Requirements bodyDemand}
      (initializer : Expression operations policy contracts world allowed scope environment initial .integer initialDemand initialRequirements)
      (body : ∀ identity, identity ∉ world → Expression operations policy contracts (world ++ [identity])
        (.cell identity :: residual) scope environment
        (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output bodyDemand (bodyRequirements identity))
      (formed : ScopedPorts.InWorld world output.port)
      (effectsBound : residual.flatMap Instance.resources ⊆ world) (admitted : residual ⊆ allowed)
      (hidden : ∀ identity, identity ∉ world → ResourceRequirements.Hides identity (bodyRequirements identity) outward) :
      Expression operations policy contracts world allowed scope environment (.resource binder initial code)
        output (initialDemand ++ bodyDemand) (.sequence initialRequirements outward)

abbrev CallableSummary (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts) :=
  CallableSources.Summary operations
    (fun world environment requests code value demand requirements =>
      Expression operations policy contracts world requests .none environment code value demand requirements)

theorem expression_from_source
    (source : Owners.Derives operations policy contracts inside world environment allowed scope before code after result demand row) :
    ∃ requirements, Expression operations policy contracts world allowed scope environment code result demand requirements := by
  induction source with
  | stable summary exported => exact ⟨_, .stable summary⟩
  | pair left right ihLeft ihRight =>
      obtain ⟨a, first⟩ := ihLeft; obtain ⟨b, second⟩ := ihRight
      exact ⟨_, .pair first second⟩
  | app function argument admitted exported ihFunction ihArgument =>
      obtain ⟨a, first⟩ := ihFunction; obtain ⟨b, second⟩ := ihArgument
      exact ⟨_, .app first second admitted⟩
  | bind initializer body ihInit ihBody =>
      obtain ⟨a, first⟩ := ihInit; obtain ⟨b, second⟩ := ihBody
      exact ⟨_, .bind first second⟩
  | branch condition yes no ihCondition ihYes ihNo =>
      obtain ⟨a, first⟩ := ihCondition; obtain ⟨b, second⟩ := ihYes; obtain ⟨c, third⟩ := ihNo
      exact ⟨_, .branch first second third (Owners.branch_demands_agree yes no)⟩
  | perform known admitted operand formed exported ih =>
      obtain ⟨a, checked⟩ := ih
      exact ⟨_, .perform known admitted checked formed⟩
  | resume known resolved permission operand transition admitted formed ih =>
      obtain ⟨a, checked⟩ := ih
      exact ⟨_, .resume known resolved permission checked admitted formed⟩
  | discard known resolved permission unprotected closable transition admitted =>
      exact ⟨_, .discard known resolved permission unprotected admitted⟩
  | cleanup callback body admitted exported ihCallback ihBody =>
      obtain ⟨a, first⟩ := ihCallback; obtain ⟨b, second⟩ := ihBody
      exact ⟨_, .cleanup first second admitted⟩
  | resource initializer body formed effectsBound admitted outward exported ih =>
      obtain ⟨requirements, initial⟩ := ih
      exact ⟨_, .resource initial (fun identity fresh =>
        CallableSources.from_legacy (body identity fresh) (fun _ _ _ _ _ _ source => .stable source)) formed effectsBound admitted outward⟩

theorem expression_value_demand
    (source : Expression operations policy contracts world allowed scope environment code result demand requirements)
    (isValue : code.IsValue) : demand = [] := by
  induction source using Expression.rec (motive_2 := fun _ _ _ _ _ _ _ => True) with
  | stable summary => rfl
  | callable summary ih => rfl
  | lambda body outward formed ih => rfl
  | purePair left right ihLeft ihRight => rfl
  | pair left right ihLeft ihRight => simp only [ihLeft isValue.1, ihRight isValue.2, List.nil_append]
  | app | bind | branch | perform | handler | resume | discard | cleanup | resource | scopedResource => cases isValue
  | _ => intros; trivial

theorem expression_ports
    (source : Expression operations policy contracts world allowed scope environment code result demand requirements)
    (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket) :
    ScopedPorts.Typed operations.ports world environment.ports ticket allowed code result.port := by
  induction source using Expression.rec
      (motive_2 := fun world environment allowed code result _ _ => ∀ ticket,
        ScopedPorts.Typed operations.ports world environment.ports ticket allowed code result.port)
      generalizing ticket with
  | stable summary => exact CoherentSourceTypes.port_typing summary ticket
  | callable summary ih => exact ih ticket
  | lambda body outward formed ih =>
      exact .lambda (by simpa only [ports_extend] using ih ScopedPorts.EffectScope.none) formed
  | purePair left right ihLeft ihRight => exact .pair (ihLeft scopeTyped) (ihRight scopeTyped)
  | pair left right ihLeft ihRight => exact .pair (ihLeft scopeTyped) (ihRight scopeTyped)
  | app function argument admitted ihFunction ihArgument => exact .app (ihFunction scopeTyped) (ihArgument scopeTyped) admitted
  | bind initializer body ihInit ihBody => exact .bind (ihInit scopeTyped) (by simpa only [ports_extend] using ihBody scopeTyped)
  | branch condition yes no same ihCondition ihYes ihNo => exact .branch (ihCondition scopeTyped) (ihYes scopeTyped) (ihNo scopeTyped)
  | perform known admitted operand formed ih => exact .perform (port_lookup known) admitted (ih scopeTyped) formed
  | handler body clauses capabilities coverage unique admitted table modes ih =>
      exact .handle (ih scopeTyped) clauses coverage unique admitted
  | resume known resolved permission operand admitted formed ih =>
      have same := Owners.scope_resolved scopeTyped known resolved
      subst ticket
      exact .resume (ih scopeTyped) admitted formed
  | discard known resolved permission unprotected admitted =>
      have same := Owners.scope_resolved scopeTyped known resolved
      subst ticket
      exact .discard admitted
  | cleanup callback body admitted ihCallback ihBody => exact .cleanup (ihCallback scopeTyped) (ihBody scopeTyped) admitted
  | resource initializer body formed effectsBound admitted outward ihInit ihBody =>
      exact .resource (ihInit scopeTyped) (fun identity fresh => ihBody identity fresh ticket) formed effectsBound admitted
  | scopedResource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      exact .resource (ihInit scopeTyped) (fun identity fresh => ihBody identity fresh scopeTyped) formed effectsBound admitted
  | summaryUnit =>
      rename_i ticket
      exact .unit
  | summaryBoolean =>
      rename_i ticket
      exact .boolean
  | summaryInteger =>
      rename_i ticket
      exact .integer
  | summaryReference issued =>
      rename_i ticket
      exact .reference issued
  | summaryVariable known formed =>
      rename_i ticket
      exact .variable (by simp [Environment.ports, known]) formed
  | summaryPair left right ihLeft ihRight =>
      rename_i ticket
      exact .pair (ihLeft ticket) (ihRight ticket)
  | summaryLambda body outward formed ih =>
      rename_i ticket
      exact .lambda (by simpa only [ports_extend] using ih ScopedPorts.EffectScope.none) formed
  | summaryApp function argument admitted ihFunction ihArgument =>
      rename_i ticket
      exact .app (ihFunction ticket) (ihArgument ticket) admitted
  | summaryBind initializer body ihInit ihBody =>
      rename_i ticket
      exact .bind (ihInit ticket) (by simpa only [ports_extend] using ihBody ticket)
  | summaryBranch condition yes no ihCondition ihYes ihNo =>
      rename_i ticket
      exact .branch (ihCondition ticket) (ihYes ticket) (ihNo ticket)
  | summaryPerform known admitted operand formed ih =>
      rename_i ticket
      exact .perform (port_lookup known) admitted (ih ticket) formed
  | summaryCleanup callback body admitted ihCallback ihBody =>
      rename_i ticket
      exact .cleanup (ihCallback ticket) (ihBody ticket) admitted
  | summaryResource initializer body formed effectsBound admitted outward ihInit ihBody =>
      rename_i ticket
      exact .resource (ihInit ticket) (fun identity fresh => ihBody identity fresh ticket) formed effectsBound admitted

/-- Shared evidence for values, retaining full source bodies in callable
    annotations. The stable case also preserves existing empty-row summaries. -/
inductive ValueSummary (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (world : List Nat) (environment : Environment) (allowed : List Instance) : Code → Value → Prop where
  | stable (summary : Summary operations world environment allowed code value []) : ValueSummary operations policy contracts world environment allowed code value
  | callable (summary : CallableSummary operations policy contracts world environment allowed code value []) :
      ValueSummary operations policy contracts world environment allowed code value
  | pair (left : ValueSummary operations policy contracts world environment allowed a first)
      (right : ValueSummary operations policy contracts world environment allowed b second) :
      ValueSummary operations policy contracts world environment allowed (.pair a b) (.pair first second)
  | lambda (body : Expression operations policy contracts world requests .none
        (environment.extend parameter input) code output bodyDemand bodyRequirements)
      (outward : RecursiveOutward.Outward bodyRequirements (some latent))
      (formed : ScopedPorts.InWorld world (Value.function input output requests latent).port) :
      ValueSummary operations policy contracts world environment allowed (.lambda parameter code) (.function input output requests latent)

theorem value_summary
    (source : Expression operations policy contracts world allowed scope environment code result demand requirements)
    (isValue : code.IsValue) : ValueSummary operations policy contracts world environment allowed code result := by
  induction source using Expression.rec (motive_2 := fun _ _ _ _ _ _ _ => True) with
  | stable summary => exact .stable (CoherentSourceTypes.value_row summary isValue ▸ summary)
  | callable summary ih => exact .callable (CallableSources.value_row summary isValue ▸ summary)
  | lambda body outward formed ih => exact .lambda body outward formed
  | pair left right ihLeft ihRight => exact .pair (ihLeft isValue.1) (ihRight isValue.2)
  | purePair left right ihLeft ihRight => exact .pair (ihLeft isValue.1) (ihRight isValue.2)
  | app | bind | branch | perform | handler | resume | discard | cleanup | resource | scopedResource => cases isValue
  | _ => intros; trivial

theorem ValueSummary.expression (source : ValueSummary operations policy contracts world environment allowed code value)
    (scope : Execution.Scope) : Expression operations policy contracts world allowed scope environment code value [] (.request [] []) := by
  induction source generalizing scope with
  | stable summary => exact .stable summary
  | callable summary => exact .callable summary
  | pair left right ihLeft ihRight => exact .purePair (ihLeft scope) (ihRight scope)
  | lambda body outward formed => exact .lambda body outward formed

theorem ValueSummary.ports (source : ValueSummary operations policy contracts world environment allowed code value)
    (ticket : ScopedPorts.Ticket) : ScopedPorts.Typed operations.ports world environment.ports ticket allowed code value.port := by
  induction source with
  | stable summary => exact CoherentSourceTypes.port_typing summary ticket
  | callable summary => exact CallableSources.port_typing summary (fun _ _ _ _ _ _ _ body => expression_ports body .none) ticket
  | pair left right ihLeft ihRight => exact .pair ihLeft ihRight
  | lambda body outward formed => exact .lambda (by simpa only [ports_extend] using expression_ports body .none) formed

theorem ValueSummary.change_allowed (source : ValueSummary operations policy contracts world environment allowed code value)
    (isValue : code.IsValue) (next : List Instance) : ValueSummary operations policy contracts world environment next code value := by
  induction source with
  | stable summary => exact .stable (CoherentSourceTypes.value_allowed summary isValue next)
  | callable summary => exact .callable (CallableSources.value_allowed summary isValue next)
  | pair left right ihLeft ihRight => exact .pair (ihLeft isValue.1) (ihRight isValue.2)
  | lambda body outward formed => exact .lambda body outward formed

inductive Context (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (world : List Nat) (environment : Environment) (allowed : List Instance) (scope : Execution.Scope) :
    ScopedExecution.Context → Value → Value → (demand : List Nat) → Requirements demand → Prop where
  | pairLeft (right : Expression operations policy contracts world allowed scope environment code output demand requirements) :
      Context operations policy contracts world environment allowed scope (.pairLeft code) input (.pair input output) demand requirements
  | pairRight (left : ValueSummary operations policy contracts world environment allowed code input) :
      Context operations policy contracts world environment allowed scope (.pairRight code) output (.pair input output) [] (.request [] [])
  | appFunction (argument : Expression operations policy contracts world allowed scope environment code input demand requirements)
      (admitted : requests ⊆ allowed) :
      Context operations policy contracts world environment allowed scope (.appFunction code) (.function input output requests latent)
        output demand (.emitAfter requirements [] latent)
  | appArgument (function : ValueSummary operations policy contracts world environment allowed code (.function input output requests latent))
      (admitted : requests ⊆ allowed) :
      Context operations policy contracts world environment allowed scope (.appArgument code) input output [] (.request [] latent)
  | bind (body : Expression operations policy contracts world allowed scope (environment.extend parameter input) code output demand requirements) :
      Context operations policy contracts world environment allowed scope (.bind parameter code) input output demand requirements
  | branch (yesSource : Expression operations policy contracts world allowed scope environment a output yesDemand yes)
      (noSource : Expression operations policy contracts world allowed scope environment b output noDemand no)
      (same : yesDemand.Perm noDemand) :
      Context operations policy contracts world environment allowed scope (.branch a b) .boolean output yesDemand (.choice yes no same)
  | perform (known : operations effect operation = some (input, output)) (admitted : effect ∈ allowed)
      (formed : ScopedPorts.InWorld world output.port) :
      Context operations policy contracts world environment allowed scope (.perform (Instantiation.freezeEffect effect) operation)
        input output [] (.request [] [⟨effect, operation, false⟩])
  | resume (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
      (permission : (policy binder).resume = true)
      (admitted : contract.resumeEffects ⊆ allowed) (formed : ScopedPorts.InWorld world contract.answer.port) :
      Context operations policy contracts world environment allowed scope (.resume binder) contract.input contract.answer
        (owner :: contract.resumeDemand) (.invoke ⟨owner, .resume⟩ contract.resumeDemand [])
  | cleanup (body : Expression operations policy contracts world allowed scope environment code output demand requirements)
      (admitted : requests ⊆ allowed) :
      Context operations policy contracts world environment allowed scope (.cleanup code) (.function .unit .unit requests latent)
        output demand (.emitAfter requirements [] (qualify true latent))
  | resource {bodyRow : Nat → Footprint}
      (body : ∀ identity, identity ∉ world → CallableSources.Summary operations
        (fun world environment requests code value demand requirements =>
          Expression operations policy contracts world requests .none environment code value demand requirements)
        (world ++ [identity]) environment (.cell identity :: residual)
        (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output (bodyRow identity))
      (formed : ScopedPorts.InWorld world output.port)
      (effectsBound : residual.flatMap Instance.resources ⊆ world) (admitted : residual ⊆ allowed)
      (outward : ∀ identity, identity ∉ world → CallableProtection.outsideCell identity (bodyRow identity) = raw) :
      Context operations policy contracts world environment allowed scope (.resource binder code) .integer output [] (.request [] raw)
  | scopedResource {bodyRequirements : Nat → Requirements demand}
      (body : ∀ identity, identity ∉ world → Expression operations policy contracts (world ++ [identity])
        (.cell identity :: residual) scope environment
        (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output demand (bodyRequirements identity))
      (formed : ScopedPorts.InWorld world output.port)
      (effectsBound : residual.flatMap Instance.resources ⊆ world) (admitted : residual ⊆ allowed)
      (hidden : ∀ identity, identity ∉ world → ResourceRequirements.Hides identity (bodyRequirements identity) outward) :
      Context operations policy contracts world environment allowed scope (.resource binder code) .integer output demand outward

theorem context_from_source
    (source : SharedSourceSegments.Context operations policy contracts inside world environment allowed scope position before input after output demand row) :
    ∃ requirements, Context operations policy contracts world environment allowed scope position input output demand requirements := by
  cases source with
  | pairLeft right => obtain ⟨a, checked⟩ := expression_from_source right; exact ⟨_, .pairLeft checked⟩
  | pairRight left => exact ⟨_, .pairRight (.stable left)⟩
  | appFunction argument admitted exported => obtain ⟨a, checked⟩ := expression_from_source argument; exact ⟨_, .appFunction checked admitted⟩
  | appArgument function admitted exported => exact ⟨_, .appArgument (.stable function) admitted⟩
  | bind body => obtain ⟨a, checked⟩ := expression_from_source body; exact ⟨_, .bind checked⟩
  | branch yes no =>
      obtain ⟨a, first⟩ := expression_from_source yes; obtain ⟨b, second⟩ := expression_from_source no
      exact ⟨_, .branch first second (Owners.branch_demands_agree yes no)⟩
  | perform known admitted formed exported => exact ⟨_, .perform known admitted formed⟩
  | resume known resolved permission transition admitted formed => exact ⟨_, .resume known resolved permission admitted formed⟩
  | resource body formed effectsBound admitted outward exported => exact ⟨_, .resource
      (fun identity fresh => CallableSources.from_legacy (body identity fresh) (fun _ _ _ _ _ _ source => .stable source))
      formed effectsBound admitted outward⟩
  | cleanup body admitted exported => obtain ⟨a, checked⟩ := expression_from_source body; exact ⟨_, .cleanup checked admitted⟩

theorem context_ports
    (source : Context operations policy contracts world environment allowed scope position input output demand requirements)
    (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket) :
    ScopedPorts.ContextTyped operations.ports world environment.ports ticket allowed position input.port output.port := by
  cases source with
  | pairLeft right => exact .pairLeft (expression_ports right scopeTyped)
  | pairRight left => exact .pairRight (left.ports ticket)
  | appFunction argument admitted => exact .appFunction (expression_ports argument scopeTyped) admitted
  | appArgument function admitted => exact .appArgument (function.ports ticket) admitted
  | bind body => exact .bind (by simpa only [ports_extend] using expression_ports body scopeTyped)
  | branch yes no same => exact .branch (expression_ports yes scopeTyped) (expression_ports no scopeTyped)
  | perform known admitted formed => exact .perform (port_lookup known) admitted formed
  | resume known resolved permission admitted formed =>
      have same := Owners.scope_resolved scopeTyped known resolved
      subst ticket
      exact .resume admitted formed
  | cleanup body admitted => exact .cleanup (expression_ports body scopeTyped) admitted
  | resource body formed effectsBound admitted outward =>
      exact .resource (fun identity fresh => CallableSources.port_typing (body identity fresh)
        (fun _ _ _ _ _ _ _ current => expression_ports current .none) ticket) formed effectsBound admitted
  | scopedResource body formed effectsBound admitted hidden =>
      exact .resource (fun identity fresh => expression_ports (body identity fresh) scopeTyped) formed effectsBound admitted

inductive Frame (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts) (world : List Nat) :
    ExecFrame → Value → Value → (demand : List Nat) → Requirements demand → Prop where
  | plain (source : Context operations policy contracts world Environment.empty allowed plain.scope plain.context input output demand requirements)
      (scopeTyped : ScopedPorts.EffectScope contracts.ports plain.scope ticket)
      (inputAnnotation : input.port = ScopedPorts.eraseType plain.input)
      (outputAnnotation : output.port = ScopedPorts.eraseType plain.output) :
      Frame operations policy contracts world (.plain plain) input output demand requirements
  | handler (typed : ScopedPorts.FrameTyped operations.ports contracts.ports.types world (.handler handler))
      (annotation : answer.port = ScopedPorts.eraseType handler.answer) :
      Frame operations policy contracts world (.handler handler) answer answer [] (.request [] [])
  | cell (scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types scope)
      (noEscape : identity ∉ (ScopedPorts.eraseType answer).resources)
      (annotation : result.port = ScopedPorts.eraseType answer) :
      Frame operations policy contracts world (.cell identity payload scope answer) result result [] (.request [] [])
  | armed (scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types action.scope)
      (callback : ValueSummary operations policy contracts world Environment.empty [] action.action (.function .unit .unit action.requests latent))
      (annotation : result.port = ScopedPorts.eraseType action.answer) :
      Frame operations policy contracts world (.armed action) result result [] (.request [] (qualify true latent))
  | running (scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types action.scope)
      (callback : ValueSummary operations policy contracts world Environment.empty [] action.action (.function .unit .unit action.requests latent))
      (saved : ValueSummary operations policy contracts world Environment.empty [] value result)
      (annotation : result.port = ScopedPorts.eraseType action.answer) :
      Frame operations policy contracts world (.running action value closed) .unit result [] (.request [] [])
  | closing (scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types scope) :
      Frame operations policy contracts world (.closing identity scope) .unit .unit [] (.request [] [])
  | retiring (known : contracts owner = some contract) :
      Frame operations policy contracts world (.retiring owner) .unit .unit [owner] (.retire owner)

theorem frame_from_source
    (source : SharedSourceSegments.Frame operations policy contracts inside world entry before input after output demand row) :
    ∃ requirements, Frame operations policy contracts world entry input output demand requirements := by
  cases source with
  | plain source scopeTyped inputAnnotation outputAnnotation =>
      obtain ⟨requirements, checked⟩ := context_from_source source
      exact ⟨_, .plain checked scopeTyped inputAnnotation outputAnnotation⟩
  | handler typed annotation => exact ⟨_, .handler typed annotation⟩
  | cell scopeKnown noEscape annotation => exact ⟨_, .cell scopeKnown noEscape annotation⟩
  | armed scopeKnown callback annotation exported => exact ⟨_, .armed scopeKnown (.stable callback) annotation⟩
  | running scopeKnown callback saved annotation => exact ⟨_, .running scopeKnown (.stable callback) (.stable saved) annotation⟩
  | closing scopeKnown => exact ⟨_, .closing scopeKnown⟩
  | retiring known transition => exact ⟨_, .retiring known⟩

theorem frame_annotations (source : Frame operations policy contracts world entry input output demand requirements) :
    input.port = ScopedPorts.eraseType entry.erase.input ∧ output.port = ScopedPorts.eraseType entry.erase.output := by
  cases source with
  | plain source scopeTyped inputAnnotation outputAnnotation => exact ⟨inputAnnotation, outputAnnotation⟩
  | handler typed annotation | cell scopeKnown noEscape annotation | armed scopeKnown callback annotation => exact ⟨annotation, annotation⟩
  | running scopeKnown callback saved annotation => exact ⟨rfl, annotation⟩
  | closing | retiring => exact ⟨rfl, rfl⟩

theorem frame_ports (source : Frame operations policy contracts world entry input output demand requirements) :
    ScopedPorts.FrameTyped operations.ports contracts.ports.types world entry := by
  cases source with
  | plain source scopeTyped inputAnnotation outputAnnotation =>
      have typed := context_ports source scopeTyped
      rw [inputAnnotation, outputAnnotation] at typed
      exact .plain (ScopedPorts.effect_scope_has_types scopeTyped) typed
  | handler typed annotation => exact typed
  | cell scopeKnown noEscape annotation => exact .cell scopeKnown noEscape
  | armed scopeKnown callback annotation => exact .armed scopeKnown (callback.ports .none)
  | running scopeKnown callback saved annotation =>
      exact .running scopeKnown (callback.ports .none) (annotation ▸ saved.ports .none)
  | closing scopeKnown => exact .closing scopeKnown
  | retiring known => exact .retiring (SharedSourceSegments.types_lookup known)

/-- The collected store contains a resume template for every retained live
    capture, including dormant nested captures. Closing templates are separate. -/
inductive Segment (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (world : List Nat) :
    Stack → Value → Value → (demand : List Nat) → Requirements demand → Store → Prop where
  | nil : Segment operations policy contracts tables world .nil result result [] (.request [] []) []
  | push (head : Frame operations policy contracts world entry input middle headDemand first)
      (tail : Segment operations policy contracts tables world rest middle output tailDemand second records) :
      Segment operations policy contracts tables world (.push entry rest) input output
        (headDemand ++ tailDemand) (.sequence (first.prepend (OwnerPhases.ofStack tables rest)) second) records
  | live (known : contracts owner = some contract)
      (inputAnnotation : contract.input.port = ScopedPorts.eraseType inputType)
      (answerAnnotation : contract.answer.port = ScopedPorts.eraseType answerType)
      (scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types caller)
      (held : contract.held = ProtectionContexts.protectedMode capture.erase)
      (saved : Segment operations policy contracts tables world capture contract.input contract.answer contract.resumeDemand body nested)
      (tail : Segment operations policy contracts tables world rest contract.answer output demand requirements remaining) :
      Segment operations policy contracts tables world (.live owner inputType answerType capture caller rest) contract.answer output
        demand (.sequence (.spent owner) requirements) ((⟨owner, .resume⟩, ⟨contract.resumeDemand, body⟩) :: (nested ++ remaining))
  | spent (known : contracts owner = some contract)
      (answerAnnotation : contract.answer.port = ScopedPorts.eraseType answerType)
      (scopeKnown : ScopedPorts.ScopeKnown contracts.ports.types caller)
      (tail : Segment operations policy contracts tables world rest contract.answer output demand requirements records) :
      Segment operations policy contracts tables world (.spent owner answerType caller rest) contract.answer output
        demand (.sequence (.spent owner) requirements) records

theorem segment_from_source
    (source : SharedSourceSegments.Segment operations policy contracts tables world fixed stack before input after output demand row) :
    ∃ requirements records, Segment operations policy contracts tables world stack input output demand requirements records := by
  induction source with
  | nil => exact ⟨_, _, .nil⟩
  | push head tail ih =>
      obtain ⟨first, frame⟩ := frame_from_source head
      obtain ⟨second, records, rest⟩ := ih
      exact ⟨_, records, .push frame rest⟩
  | live known inputAnnotation answerAnnotation scopeKnown held consumed saved covered tail ihSaved ihTail =>
      obtain ⟨body, nested, captured⟩ := ihSaved
      obtain ⟨requirements, remaining, rest⟩ := ihTail
      exact ⟨_, _, .live known inputAnnotation answerAnnotation scopeKnown held captured rest⟩
  | spent known answerAnnotation scopeKnown consumed tail ih =>
      obtain ⟨requirements, records, rest⟩ := ih
      exact ⟨_, records, .spent known answerAnnotation scopeKnown rest⟩

theorem segment_ports (source : Segment operations policy contracts tables world stack input output demand requirements records) :
    ScopedPorts.StackTyped operations.ports contracts.ports.types world stack input.port output.port := by
  induction source with
  | nil => exact .nil
  | push head tail ih =>
      have annotations := frame_annotations head
      rw [annotations.2] at ih
      rw [annotations.1]
      exact .push (frame_ports head) ih
  | live known inputAnnotation answerAnnotation scopeKnown held saved tail ihSaved ihTail =>
      rw [inputAnnotation, answerAnnotation] at ihSaved
      rw [answerAnnotation] at ihTail ⊢
      exact .live (by simpa only [inputAnnotation, answerAnnotation] using SharedSourceSegments.types_lookup known) scopeKnown ihSaved ihTail
  | spent known answerAnnotation scopeKnown tail ih =>
      rw [answerAnnotation] at ih ⊢
      exact .spent (by simpa only [answerAnnotation] using SharedSourceSegments.types_lookup known) scopeKnown ih

inductive CapturedIn (owner : Nat) (capture : Stack) : Stack → Prop where
  | here : CapturedIn owner capture (.live owner input answer capture caller rest)
  | push (located : CapturedIn owner capture rest) : CapturedIn owner capture (.push frame rest)
  | saved (located : CapturedIn owner capture nested) : CapturedIn owner capture (.live other input answer nested caller rest)
  | tail (located : CapturedIn owner capture rest) : CapturedIn owner capture (.live other input answer nested caller rest)
  | spent (located : CapturedIn owner capture rest) : CapturedIn owner capture (.spent other answer caller rest)

/-- Active selection follows only the caller spine and stops at a matching
    consumed owner. Saved bodies remain dormant until restored. -/
inductive ActiveCapture (owner : Nat) (capture : Stack) : Stack → Prop where
  | here : ActiveCapture owner capture (.live owner input answer capture caller rest)
  | push (selected : ActiveCapture owner capture rest) : ActiveCapture owner capture (.push frame rest)
  | live (different : owner ≠ other) (selected : ActiveCapture owner capture rest) :
      ActiveCapture owner capture (.live other input answer saved caller rest)
  | spent (different : owner ≠ other) (selected : ActiveCapture owner capture rest) :
      ActiveCapture owner capture (.spent other answer caller rest)

theorem active_capture_located (selected : ActiveCapture owner capture stack) : CapturedIn owner capture stack := by
  induction selected with
  | here => exact .here
  | push selected ih => exact .push ih
  | live different selected ih => exact .tail ih
  | spent different selected ih => exact .spent ih

theorem active_capture_decompose (selected : ActiveCapture owner capture stack) :
    ∃ (front : Stack), ∃ input answer caller tail, stack = front.append (.live owner input answer capture caller tail) := by
  induction selected with
  | here => exact ⟨.nil, _, _, _, _, rfl⟩
  | @push rest frame selected ih =>
      obtain ⟨front, input, answer, caller, tail, same⟩ := ih
      exact ⟨.push frame front, input, answer, caller, tail, by simp only [Stack.append, same]⟩
  | @live other rest input answer saved caller different selected ih =>
      obtain ⟨front, targetInput, targetAnswer, targetCaller, tail, same⟩ := ih
      exact ⟨.live other input answer saved caller front, targetInput, targetAnswer, targetCaller, tail,
        by simp only [Stack.append, same]⟩
  | @spent other rest answer caller different selected ih =>
      obtain ⟨front, targetInput, targetAnswer, targetCaller, tail, same⟩ := ih
      exact ⟨.spent other answer caller front, targetInput, targetAnswer, targetCaller, tail,
        by simp only [Stack.append, same]⟩

theorem consume_frame :
    OwnerPhases.consume owner (OwnerPhases.frameEntry tables frame :: rest) =
      (OwnerPhases.consume owner rest).map (OwnerPhases.frameEntry tables frame :: ·) := by
  cases frame <;> rfl

theorem consume_active_capture (selected : OwnerPhases.consume owner (OwnerPhases.ofStack tables stack) = some waiting) :
    ∃ capture, ActiveCapture owner capture stack := by
  induction stack generalizing waiting with
  | nil => cases selected
  | push frame rest ih =>
      simp only [OwnerPhases.ofStack, consume_frame] at selected
      cases found : OwnerPhases.consume owner (OwnerPhases.ofStack tables rest) with
      | none => simp [found] at selected
      | some next => obtain ⟨capture, located⟩ := ih found; exact ⟨capture, .push located⟩
  | live other input answer saved caller rest ihSaved ihRest =>
      by_cases same : owner = other
      · subst other; exact ⟨saved, .here⟩
      · simp only [OwnerPhases.ofStack, OwnerPhases.consume, same, if_false] at selected
        cases found : OwnerPhases.consume owner (OwnerPhases.ofStack tables rest) with
        | none => simp [found] at selected
        | some next => obtain ⟨capture, located⟩ := ihRest found; exact ⟨capture, .live same located⟩
  | spent other answer caller rest ih =>
      by_cases same : owner = other
      · simp [OwnerPhases.ofStack, OwnerPhases.consume, same] at selected
      · simp only [OwnerPhases.ofStack, OwnerPhases.consume, same, if_false] at selected
        cases found : OwnerPhases.consume owner (OwnerPhases.ofStack tables rest) with
        | none => simp [found] at selected
        | some next => obtain ⟨capture, located⟩ := ih found; exact ⟨capture, .spent same located⟩

theorem active_capture_selection (selected : ActiveCapture owner capture stack) :
    ∃ waiting, OwnerPhases.Consumes owner (OwnerPhases.ofStack tables stack) waiting := by
  induction selected with
  | here => exact ⟨_, .hit⟩
  | @push rest frame selected ih =>
      obtain ⟨waiting, next⟩ := ih
      cases frame <;> exact ⟨_, .ordinary next⟩
  | live different selected ih => obtain ⟨waiting, next⟩ := ih; exact ⟨_, .live different next⟩
  | spent different selected ih => obtain ⟨waiting, next⟩ := ih; exact ⟨_, .spent different next⟩

theorem captured_in_owned (located : CapturedIn owner capture stack) : owner ∈ ownedTickets stack := by
  induction located with
  | here => simp [ownedTickets]
  | @push rest frame located ih => cases frame <;> simp_all [ownedTickets]
  | saved located ih => exact List.mem_cons_of_mem _ (List.mem_append_left _ ih)
  | tail located ih => exact List.mem_cons_of_mem _ (List.mem_append_right _ ih)
  | spent located ih => exact ih

theorem captured_in_unique (unique : (ownedTickets stack).Nodup)
    (first : CapturedIn owner capture stack) (second : CapturedIn owner other stack) : capture = other := by
  induction stack generalizing capture other with
  | nil => cases first
  | push frame rest ih =>
      have restUnique : (ownedTickets rest).Nodup := by cases frame <;> simp_all [ownedTickets]
      cases first with
      | push first => cases second with
          | push second => exact ih restUnique first second
  | live boundary input answer saved caller rest ihSaved ihRest =>
      have absent := (List.nodup_cons.mp unique).1
      have parts := List.nodup_append.mp (List.nodup_cons.mp unique).2
      cases first with
      | here => cases second with
          | here => rfl
          | saved second => exact False.elim (absent (List.mem_append_left _ (captured_in_owned second)))
          | tail second => exact False.elim (absent (List.mem_append_right _ (captured_in_owned second)))
      | saved first => cases second with
          | here => exact False.elim (absent (List.mem_append_left _ (captured_in_owned first)))
          | saved second => exact ihSaved parts.1 first second
          | tail second => exact False.elim (parts.2.2 owner (captured_in_owned first) owner (captured_in_owned second) rfl)
      | tail first => cases second with
          | here => exact False.elim (absent (List.mem_append_right _ (captured_in_owned first)))
          | saved second => exact False.elim (parts.2.2 owner (captured_in_owned second) owner (captured_in_owned first) rfl)
          | tail second => exact ihRest parts.2.1 first second
  | spent boundary answer caller rest ih =>
      cases first with
      | spent first => cases second with
          | spent second => exact ih unique first second

inductive Certified (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (world : List Nat) (root : Stack) : Key → RecursiveRequirements.Template → Prop where
  | resume (located : CapturedIn owner capture root) (known : contracts owner = some contract)
      (saved : Segment operations policy contracts tables world capture contract.input contract.answer contract.resumeDemand requirements records) :
      Certified operations policy contracts tables world root ⟨owner, .resume⟩ ⟨contract.resumeDemand, requirements⟩

theorem certified_transport (source : Certified operations policy contracts tables world first key body)
    (move : ∀ owner capture, CapturedIn owner capture first → CapturedIn owner capture second) :
    Certified operations policy contracts tables world second key body := by
  cases source with
  | resume located known saved => exact .resume (move _ _ located) known saved

theorem records_certified (source : Segment operations policy contracts tables world stack input output demand requirements records)
    (member : (key, body) ∈ records) : Certified operations policy contracts tables world stack key body := by
  induction source with
  | nil => cases member
  | push head tail ih => exact certified_transport (ih member) (fun _ _ located => .push located)
  | live known inputAnnotation answerAnnotation scopeKnown held saved tail ihSaved ihTail =>
      simp only [List.mem_cons, List.mem_append] at member
      rcases member with equal | nested | remaining
      · cases equal; exact .resume .here known saved
      · exact certified_transport (ihSaved nested) (fun _ _ located => .saved located)
      · exact certified_transport (ihTail remaining) (fun _ _ located => .tail located)
  | spent known answerAnnotation scopeKnown tail ih => exact certified_transport (ih member) (fun _ _ located => .spent located)

theorem lookup_member (known : RecursiveRequirements.lookup key records = some body) : (key, body) ∈ records := by
  induction records with
  | nil => cases known
  | cons entry rest ih =>
      obtain ⟨candidate, template⟩ := entry
      simp only [RecursiveRequirements.lookup] at known
      split at known
      · have same : key = candidate := by assumption
        subst candidate
        cases Option.some.inj known
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih known)

theorem lookup_certified (source : Segment operations policy contracts tables world stack input output demand requirements records)
    (known : RecursiveRequirements.lookup key records = some body) : Certified operations policy contracts tables world stack key body :=
  records_certified source (lookup_member known)

/-- Distinct runtime owners identify the selected saved body with the body
    authenticated by the first matching collected-store entry. -/
theorem certified_selected
    (source : Certified operations policy contracts tables world stack key template)
    (unique : (ownedTickets stack).Nodup)
    (selected : ActiveCapture key.owner capture stack) :
    ∃ (contract : Owners.Contract) (requirements : Requirements contract.resumeDemand) (records : Store),
      contracts key.owner = some contract ∧ template = ⟨contract.resumeDemand, requirements⟩ ∧
      Segment operations policy contracts tables world capture contract.input contract.answer
        contract.resumeDemand requirements records := by
  cases source with
  | resume located known saved =>
      have same := captured_in_unique unique located (active_capture_located selected)
      cases same
      exact ⟨_, _, _, known, rfl, saved⟩

/-- A recursively checked resume from a source-derived store has an actual
    runtime step restoring exactly the source body used by the recursive check.
    This is a local progress theorem, not preservation of the whole checker. -/
theorem checked_resume_step
    (source : Segment operations policy contracts tables world stack input output pendingDemand pending records)
    (unique : (ownedTickets stack).Nodup)
    (checked : RecursiveRequirements.Checked records (OwnerPhases.ofStack tables stack) before
      (.invoke ⟨owner, .resume⟩ demand []) row)
    (resolved : scope.resolve binder = some owner) (closed : ClosedValue value) :
    ∃ (capture front : Stack) (inputType answerType : Ty) (caller : Execution.Scope) (tail : Stack)
      (contract : Owners.Contract) (requirements : Requirements contract.resumeDemand) (nested : Store),
      stack = front.append (.live owner inputType answerType capture caller tail) ∧
      contracts owner = some contract ∧ demand = contract.resumeDemand ∧
      Segment operations policy contracts tables world capture contract.input contract.answer
        contract.resumeDemand requirements nested ∧
      RecursiveRequirements.lookup ⟨owner, .resume⟩ records = some ⟨contract.resumeDemand, requirements⟩ ∧
      RecursiveRequirements.Checked records (OwnerPhases.ofStack tables stack) (OwnerPhaseTransitions.spend before owner)
        requirements row ∧
      RawStep ⟨.resume binder value, scope, stack⟩
        ⟨value, scope, capture.append (front.append (.spent owner answerType caller tail))⟩ [] [.ticket owner] ∧
      OwnerPhaseTransitions.Trace (OwnerPhaseTransitions.available (ownedTickets stack)) [owner]
        (OwnerPhaseTransitions.available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail))))) := by
  obtain ⟨body, waiting, known, ready, selection, bodyChecked⟩ := RecursiveRequirements.checked_invocation checked
  obtain ⟨capture, active⟩ := consume_active_capture (OwnerPhases.consumes_sound selection)
  obtain ⟨contract, requirements, nested, contractKnown, sameTemplate, saved⟩ :=
    certified_selected (lookup_certified source known) unique active
  have sameDemand := congrArg Sigma.fst sameTemplate
  change demand = contract.resumeDemand at sameDemand
  have sameBody := (Sigma.mk.inj sameTemplate).2
  subst demand
  cases eq_of_heq sameBody
  obtain ⟨front, inputType, answerType, caller, tail, sameStack⟩ := active_capture_decompose active
  refine ⟨capture, front, inputType, answerType, caller, tail, contract, requirements, nested,
    sameStack, contractKnown, rfl, saved, known, bodyChecked, ?_⟩
  rw [sameStack]
  exact ⟨.resume binder owner scope caller inputType answerType front capture tail value closed resolved,
    OwnerPhaseTransitions.resume_phase_trace (by simpa only [sameStack] using unique)⟩

inductive Configuration (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (world : List Nat) :
    Execution.Scope → Code → Stack → Value → (demand : List Nat) → Requirements demand → Store → Prop where
  | checked (current : Expression operations policy contracts world allowed scope Environment.empty code input currentDemand currentRequirements)
      (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket)
      (pending : Segment operations policy contracts tables world stack input output pendingDemand pendingRequirements records) :
      Configuration operations policy contracts tables world scope code stack output (currentDemand ++ pendingDemand)
        (.sequence (currentRequirements.prepend (OwnerPhases.ofStack tables stack)) pendingRequirements) records

theorem configuration_from_source
    (source : SharedSourceSegments.Source operations policy contracts tables world fixed outside scope code stack before after output demand row) :
    ∃ requirements records, Configuration operations policy contracts tables world scope code stack output demand requirements records := by
  cases source with
  | checked current scopeTyped pending accepted =>
      obtain ⟨a, expression⟩ := expression_from_source current
      obtain ⟨b, records, segment⟩ := segment_from_source pending
      exact ⟨_, records, .checked expression scopeTyped segment⟩

theorem configuration_ports
    (source : Configuration operations policy contracts tables world scope code stack output demand requirements records) :
    ScopedPorts.ConfigurationTyped operations.ports contracts.ports.types world ⟨code, scope, stack⟩ output.port := by
  cases source with
  | checked current scopeTyped pending =>
      exact ⟨_, .checked (ScopedPorts.effect_scope_has_types scopeTyped) (expression_ports current scopeTyped), segment_ports pending⟩

theorem configuration_records
    (source : Configuration operations policy contracts tables world scope code stack output demand requirements records)
    (known : RecursiveRequirements.lookup key records = some body) : Certified operations policy contracts tables world stack key body := by
  cases source with
  | checked current scopeTyped pending => exact lookup_certified pending known

/-- This is a checked current configuration, not yet an initial-source judgment
    with preservation/progress through every future transition. -/
inductive CheckedConfiguration (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (world : List Nat) (outside : ProtectionContracts.Context)
    (scope : Execution.Scope) (code : Code) (stack : Stack) (output : Value) (demand : List Nat) (row : Footprint) : Prop where
  | checked (source : Configuration operations policy contracts tables world scope code stack output demand requirements records)
      (unique : (ownedTickets stack).Nodup)
      (evaluated : RecursiveRequirements.Checked records [] (OwnerPhaseTransitions.available (ownedTickets stack)) requirements row)
      (accepted : checkFootprint outside row = true) :
      CheckedConfiguration operations policy contracts tables world outside scope code stack output demand row

theorem check_configuration
    (source : Configuration operations policy contracts tables world scope code stack output demand requirements records)
    (unique : (ownedTickets stack).Nodup)
    (checked : RecursiveRequirements.evaluate records [] (OwnerPhaseTransitions.available (ownedTickets stack)) requirements = some row)
    (accepted : checkFootprint outside row = true) :
    CheckedConfiguration operations policy contracts tables world outside scope code stack output demand row :=
  .checked source unique (RecursiveRequirements.evaluate_sound checked) accepted

theorem checked_configuration_ports
    (source : CheckedConfiguration operations policy contracts tables world outside scope code stack output demand row) :
    ScopedPorts.ConfigurationTyped operations.ports contracts.ports.types world ⟨code, scope, stack⟩ output.port := by
  cases source with
  | checked source unique evaluated accepted => exact configuration_ports source

theorem checked_configuration_trace
    (source : CheckedConfiguration operations policy contracts tables world outside scope code stack output demand row) :
    OwnerPhaseTransitions.Trace (OwnerPhaseTransitions.available (ownedTickets stack)) demand
      (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets stack)) demand) := by
  cases source with
  | checked source unique evaluated accepted => exact RecursiveRequirements.checked_trace evaluated

theorem checked_configuration_once
    (source : CheckedConfiguration operations policy contracts tables world outside scope code stack output demand row) : demand.Nodup := by
  cases source with
  | checked source unique evaluated accepted => exact RecursiveRequirements.checked_once evaluated

theorem checked_configuration_unique
    (source : CheckedConfiguration operations policy contracts tables world outside scope code stack output demand row) :
    (ownedTickets stack).Nodup := by
  cases source with
  | checked source unique evaluated accepted => exact unique

theorem checked_configuration_resume_progress
    (source : CheckedConfiguration operations policy contracts tables world outside scope (.resume binder value) stack output demand row)
    (closed : ClosedValue value) :
    ∃ (owner : Nat) (next : ScopedExecution.Configuration),
      scope.resolve binder = some owner ∧
      RawStep ⟨.resume binder value, scope, stack⟩ next [] [.ticket owner] ∧
      OwnerPhaseTransitions.Trace (OwnerPhaseTransitions.available (ownedTickets stack)) [owner]
        (OwnerPhaseTransitions.available (ownedTickets next.stack)) := by
  cases source with
  | checked source unique evaluated accepted => cases source with
      | checked current scopeTyped pending => cases current with
          | stable summary => cases summary
          | callable summary => cases summary
          | resume known resolved permission operand admitted formed =>
              have noDemand := expression_value_demand operand closed.1
              obtain ⟨currentRow, pendingRow, currentChecked, pendingChecked, rows⟩ :=
                RecursiveRequirements.checked_sequence_parts evaluated
              have currentAt := RecursiveRequirements.checked_prepend_iff.mp currentChecked
              simp only [List.append_nil] at currentAt
              obtain ⟨operandRow, resumeRow, operandChecked, resumeChecked, currentRows⟩ :=
                RecursiveRequirements.checked_sequence_parts currentAt
              rw [noDemand] at resumeChecked
              obtain ⟨capture, front, inputType, answerType, caller, tail, contract, body, nested,
                sameStack, known, sameDemand, saved, lookup, checkedBody, step, trace⟩ :=
                  checked_resume_step pending unique resumeChecked resolved closed
              exact ⟨_, _, resolved, step, trace⟩

/-- A larger resource world retains the exact continuation requirements. -/
theorem expression_world_weaken
    (source : Expression operations policy contracts world allowed scope environment code result demand requirements)
    (larger : world ⊆ next) :
    Expression operations policy contracts next allowed scope environment code result demand requirements := by
  induction source using Expression.rec
      (motive_2 := fun world environment allowed code value row _ => ∀ next, world ⊆ next →
        CallableSummary operations policy contracts next environment allowed code value row)
      generalizing next with
  | stable summary => exact .stable (summary_world_weaken summary larger)
  | callable summary ih => exact .callable (ih next larger)
  | lambda body outward formed ih => exact .lambda (ih larger) outward (ScopedPorts.in_world_mono formed larger)
  | purePair left right ihLeft ihRight => exact .purePair (ihLeft larger) (ihRight larger)
  | pair left right ihLeft ihRight => exact .pair (ihLeft larger) (ihRight larger)
  | app function argument admitted ihFunction ihArgument => exact .app (ihFunction larger) (ihArgument larger) admitted
  | bind initializer body ihInit ihBody => exact .bind (ihInit larger) (ihBody larger)
  | branch condition yes no same ihCondition ihYes ihNo => exact .branch (ihCondition larger) (ihYes larger) (ihNo larger) same
  | perform known admitted operand formed ih => exact .perform known admitted (ih larger) (ScopedPorts.in_world_mono formed larger)
  | handler body clauses capabilities coverage unique admitted table modes ih =>
      exact .handler (ih larger) (ScopedPorts.clauses_world_weaken clauses larger) capabilities coverage unique admitted table modes
  | resume known resolved permission operand admitted formed ih =>
      exact .resume known resolved permission (ih larger) admitted (ScopedPorts.in_world_mono formed larger)
  | discard known resolved permission unprotected admitted => exact .discard known resolved permission unprotected admitted
  | cleanup callback body admitted ihCallback ihBody => exact .cleanup (ihCallback larger) (ihBody larger) admitted
  | resource initializer body formed effectsBound admitted outward ihInit ihBody =>
      exact .resource (ihInit larger)
        (fun identity fresh => ihBody identity (fun member => fresh (larger member)) (next ++ [identity])
          (ScopedExpressions.append_subset larger (List.Subset.refl _)))
        (ScopedPorts.in_world_mono formed larger) (effectsBound.trans larger) admitted
        (fun identity fresh => outward identity (fun member => fresh (larger member)))
  | scopedResource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      exact .scopedResource (ihInit larger)
        (fun identity fresh => ihBody identity (fun member => fresh (larger member))
          (ScopedExpressions.append_subset larger (List.Subset.refl _)))
        (ScopedPorts.in_world_mono formed larger) (effectsBound.trans larger) admitted
        (fun identity fresh => hidden identity (fun member => fresh (larger member)))
  | summaryUnit =>
      rename_i next larger
      exact .summaryUnit
  | summaryBoolean =>
      rename_i next larger
      exact .summaryBoolean
  | summaryInteger =>
      rename_i next larger
      exact .summaryInteger
  | summaryReference issued =>
      rename_i next larger
      exact .summaryReference (larger issued)
  | summaryVariable known formed =>
      rename_i next larger
      exact .summaryVariable known (ScopedPorts.in_world_mono formed larger)
  | summaryPair left right ihLeft ihRight =>
      rename_i next larger
      exact .summaryPair (ihLeft next larger) (ihRight next larger)
  | summaryLambda body outward formed ih =>
      rename_i next larger
      exact .summaryLambda (ih larger) outward (ScopedPorts.in_world_mono formed larger)
  | summaryApp function argument admitted ihFunction ihArgument =>
      rename_i next larger
      exact .summaryApp (ihFunction next larger) (ihArgument next larger) admitted
  | summaryBind initializer body ihInit ihBody =>
      rename_i next larger
      exact .summaryBind (ihInit next larger) (ihBody next larger)
  | summaryBranch condition yes no ihCondition ihYes ihNo =>
      rename_i next larger
      exact .summaryBranch (ihCondition next larger) (ihYes next larger) (ihNo next larger)
  | summaryPerform known admitted operand formed ih =>
      rename_i next larger
      exact .summaryPerform known admitted (ih next larger) (ScopedPorts.in_world_mono formed larger)
  | summaryCleanup callback body admitted ihCallback ihBody =>
      rename_i next larger
      exact .summaryCleanup (ihCallback next larger) (ihBody next larger) admitted
  | summaryResource initializer body formed effectsBound admitted outward ihInit ihBody =>
      rename_i next larger

      exact .summaryResource (ihInit next larger)
        (fun identity fresh => ihBody identity (fun member => fresh (larger member))
          (next ++ [identity]) (ScopedExpressions.append_subset larger (List.Subset.refl _)))
        (ScopedPorts.in_world_mono formed larger) (effectsBound.trans larger) admitted
        (fun identity fresh => outward identity (fun member => fresh (larger member)))

theorem ValueSummary.world_weaken (source : ValueSummary operations policy contracts world environment allowed code value)
    (larger : world ⊆ next) : ValueSummary operations policy contracts next environment allowed code value := by
  induction source with
  | stable summary => exact .stable (summary_world_weaken summary larger)
  | callable summary => exact .callable (CallableSources.summary_world_weaken summary
      (fun _ _ _ _ _ _ _ _ body grows => expression_world_weaken body grows) larger)
  | pair left right ihLeft ihRight => exact .pair ihLeft ihRight
  | lambda body outward formed => exact .lambda (expression_world_weaken body larger) outward (ScopedPorts.in_world_mono formed larger)

theorem context_world_weaken
    (source : Context operations policy contracts world environment allowed scope position input output demand requirements)
    (larger : world ⊆ next) :
    Context operations policy contracts next environment allowed scope position input output demand requirements := by
  cases source with
  | pairLeft right => exact .pairLeft (expression_world_weaken right larger)
  | pairRight left => exact .pairRight (left.world_weaken larger)
  | appFunction argument admitted => exact .appFunction (expression_world_weaken argument larger) admitted
  | appArgument function admitted => exact .appArgument (function.world_weaken larger) admitted
  | bind body => exact .bind (expression_world_weaken body larger)
  | branch yes no same => exact .branch (expression_world_weaken yes larger) (expression_world_weaken no larger) same
  | perform known admitted formed => exact .perform known admitted (ScopedPorts.in_world_mono formed larger)
  | resume known resolved permission admitted formed => exact .resume known resolved permission admitted (ScopedPorts.in_world_mono formed larger)
  | cleanup body admitted => exact .cleanup (expression_world_weaken body larger) admitted
  | resource body formed effectsBound admitted outward =>
      exact .resource
        (fun identity fresh => CallableSources.summary_world_weaken (body identity (fun member => fresh (larger member)))
          (fun _ _ _ _ _ _ _ _ current grows => expression_world_weaken current grows)
          (ScopedExpressions.append_subset larger (List.Subset.refl _)))
        (ScopedPorts.in_world_mono formed larger) (effectsBound.trans larger) admitted
        (fun identity fresh => outward identity (fun member => fresh (larger member)))
  | scopedResource body formed effectsBound admitted hidden =>
      exact .scopedResource
        (fun identity fresh => expression_world_weaken (body identity (fun member => fresh (larger member)))
          (ScopedExpressions.append_subset larger (List.Subset.refl _)))
        (ScopedPorts.in_world_mono formed larger) (effectsBound.trans larger) admitted
        (fun identity fresh => hidden identity (fun member => fresh (larger member)))

theorem frame_world_weaken
    (source : Frame operations policy contracts world entry input output demand requirements)
    (larger : world ⊆ next) : Frame operations policy contracts next entry input output demand requirements := by
  cases source with
  | plain source scopeTyped inputAnnotation outputAnnotation =>
      exact .plain (context_world_weaken source larger) scopeTyped inputAnnotation outputAnnotation
  | handler typed annotation => exact .handler (ScopedPorts.frame_world_weaken typed larger) annotation
  | cell scopeKnown noEscape annotation => exact .cell scopeKnown noEscape annotation
  | armed scopeKnown callback annotation => exact .armed scopeKnown (callback.world_weaken larger) annotation
  | running scopeKnown callback saved annotation =>
      exact .running scopeKnown (callback.world_weaken larger) (saved.world_weaken larger) annotation
  | closing scopeKnown => exact .closing scopeKnown
  | retiring known => exact .retiring known

/-- Both active and dormant saved computations keep their actual resume store. -/
theorem segment_world_weaken
    (source : Segment operations policy contracts tables world stack input output demand requirements records)
    (larger : world ⊆ next) :
    Segment operations policy contracts tables next stack input output demand requirements records := by
  induction source with
  | nil => exact .nil
  | push head tail ih => exact .push (frame_world_weaken head larger) ih
  | live known inputAnnotation answerAnnotation scopeKnown held saved tail ihSaved ihTail =>
      exact .live known inputAnnotation answerAnnotation scopeKnown held ihSaved ihTail
  | spent known answerAnnotation scopeKnown tail ih => exact .spent known answerAnnotation scopeKnown ih

theorem configuration_world_weaken
    (source : Configuration operations policy contracts tables world scope code stack output demand requirements records)
    (larger : world ⊆ next) :
    Configuration operations policy contracts tables next scope code stack output demand requirements records := by
  cases source with
  | checked current scopeTyped pending =>
      exact .checked (expression_world_weaken current larger) scopeTyped (segment_world_weaken pending larger)

theorem expression_extension
    (source : Expression operations policy contracts world allowed scope environment code result demand requirements)
    (extension : contracts.Extends larger) :
    Expression operations policy larger world allowed scope environment code result demand requirements := by
  induction source using Expression.rec
      (motive_2 := fun world environment allowed code value row _ =>
        CallableSummary operations policy larger world environment allowed code value row) with
  | stable summary => exact .stable summary
  | callable summary ih => exact .callable ih
  | lambda body outward formed ih => exact .lambda ih outward formed
  | purePair left right ihLeft ihRight => exact .purePair ihLeft ihRight
  | pair left right ihLeft ihRight => exact .pair ihLeft ihRight
  | app function argument admitted ihFunction ihArgument => exact .app ihFunction ihArgument admitted
  | bind initializer body ihInit ihBody => exact .bind ihInit ihBody
  | branch condition yes no same ihCondition ihYes ihNo => exact .branch ihCondition ihYes ihNo same
  | perform known admitted operand formed ih => exact .perform known admitted ih formed
  | handler body clauses capabilities coverage unique admitted table modes ih => exact .handler ih clauses capabilities coverage unique admitted table modes
  | resume known resolved permission operand admitted formed ih => exact .resume (extension _ _ known) resolved permission ih admitted formed
  | discard known resolved permission unprotected admitted => exact .discard (extension _ _ known) resolved permission unprotected admitted
  | cleanup callback body admitted ihCallback ihBody => exact .cleanup ihCallback ihBody admitted
  | resource initializer body formed effectsBound admitted outward ihInit ihBody => exact .resource ihInit ihBody formed effectsBound admitted outward
  | scopedResource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      exact .scopedResource ihInit ihBody formed effectsBound admitted hidden
  | summaryUnit => exact .summaryUnit
  | summaryBoolean => exact .summaryBoolean
  | summaryInteger => exact .summaryInteger
  | summaryReference issued => exact .summaryReference issued
  | summaryVariable known formed => exact .summaryVariable known formed
  | summaryPair left right ihLeft ihRight => exact .summaryPair ihLeft ihRight
  | summaryLambda body outward formed ih => exact .summaryLambda ih outward formed
  | summaryApp function argument admitted ihFunction ihArgument => exact .summaryApp ihFunction ihArgument admitted
  | summaryBind initializer body ihInit ihBody => exact .summaryBind ihInit ihBody
  | summaryBranch condition yes no ihCondition ihYes ihNo => exact .summaryBranch ihCondition ihYes ihNo
  | summaryPerform known admitted operand formed ih => exact .summaryPerform known admitted ih formed
  | summaryCleanup callback body admitted ihCallback ihBody => exact .summaryCleanup ihCallback ihBody admitted
  | summaryResource initializer body formed effectsBound admitted outward ihInit ihBody =>
      exact .summaryResource ihInit ihBody formed effectsBound admitted outward

theorem ValueSummary.extension (source : ValueSummary operations policy contracts world environment allowed code value)
    (extension : contracts.Extends larger) : ValueSummary operations policy larger world environment allowed code value := by
  induction source with
  | stable summary => exact .stable summary
  | callable summary => exact .callable (CallableSources.map_body summary
      (fun _ _ _ _ _ _ _ body => expression_extension body extension))
  | pair left right ihLeft ihRight => exact .pair ihLeft ihRight
  | lambda body outward formed => exact .lambda (expression_extension body extension) outward formed

theorem context_extension
    (source : Context operations policy contracts world environment allowed scope position input output demand requirements)
    (extension : contracts.Extends larger) :
    Context operations policy larger world environment allowed scope position input output demand requirements := by
  cases source with
  | pairLeft right => exact .pairLeft (expression_extension right extension)
  | pairRight left => exact .pairRight (left.extension extension)
  | appFunction argument admitted => exact .appFunction (expression_extension argument extension) admitted
  | appArgument function admitted => exact .appArgument (function.extension extension) admitted
  | bind body => exact .bind (expression_extension body extension)
  | branch yes no same => exact .branch (expression_extension yes extension) (expression_extension no extension) same
  | perform known admitted formed => exact .perform known admitted formed
  | resume known resolved permission admitted formed => exact .resume (extension _ _ known) resolved permission admitted formed
  | cleanup body admitted => exact .cleanup (expression_extension body extension) admitted
  | resource body formed effectsBound admitted outward =>
      exact .resource
        (fun identity fresh => CallableSources.map_body (body identity fresh)
          (fun _ _ _ _ _ _ _ current => expression_extension current extension)) formed effectsBound admitted outward
  | scopedResource body formed effectsBound admitted hidden =>
      exact .scopedResource (fun identity fresh => expression_extension (body identity fresh) extension)
        formed effectsBound admitted hidden

theorem frame_extension (source : Frame operations policy contracts world entry input output demand requirements)
    (extension : contracts.Extends larger) : Frame operations policy larger world entry input output demand requirements := by
  have ports := Owners.port_contracts_extension extension
  have types := ScopedPorts.effect_extension_has_type_extension ports
  cases source with
  | plain source scopeTyped inputAnnotation outputAnnotation =>
      exact .plain (context_extension source extension) (ScopedPorts.effect_scope_extension scopeTyped ports) inputAnnotation outputAnnotation
  | handler typed annotation => exact .handler (ScopedPorts.frame_typed_extension typed types) annotation
  | cell scopeKnown noEscape annotation => exact .cell (ScopedPorts.scope_known_extension scopeKnown types) noEscape annotation
  | armed scopeKnown callback annotation => exact .armed (ScopedPorts.scope_known_extension scopeKnown types) (callback.extension extension) annotation
  | running scopeKnown callback saved annotation => exact .running (ScopedPorts.scope_known_extension scopeKnown types) (callback.extension extension) (saved.extension extension) annotation
  | closing scopeKnown => exact .closing (ScopedPorts.scope_known_extension scopeKnown types)
  | retiring known => exact .retiring (extension _ _ known)

theorem segment_extension
    (source : Segment operations policy contracts tables world stack input output demand requirements records)
    (extension : contracts.Extends larger) : Segment operations policy larger tables world stack input output demand requirements records := by
  have types := ScopedPorts.effect_extension_has_type_extension (Owners.port_contracts_extension extension)
  induction source with
  | nil => exact .nil
  | push head tail ih => exact .push (frame_extension head extension) ih
  | live known inputAnnotation answerAnnotation scopeKnown held saved tail ihSaved ihTail =>
      exact .live (extension _ _ known) inputAnnotation answerAnnotation (ScopedPorts.scope_known_extension scopeKnown types) held ihSaved ihTail
  | spent known answerAnnotation scopeKnown tail ih =>
      exact .spent (extension _ _ known) answerAnnotation (ScopedPorts.scope_known_extension scopeKnown types) ih

theorem certified_extension (source : Certified operations policy contracts tables world stack key body)
    (extension : contracts.Extends larger) : Certified operations policy larger tables world stack key body := by
  cases source with
  | resume located known saved => exact .resume located (extension _ _ known) (segment_extension saved extension)

theorem configuration_extension
    (source : Configuration operations policy contracts tables world scope code stack output demand requirements records)
    (extension : contracts.Extends larger) : Configuration operations policy larger tables world scope code stack output demand requirements records := by
  cases source with
  | checked current scopeTyped pending =>
      exact .checked (expression_extension current extension)
        (ScopedPorts.effect_scope_extension scopeTyped (Owners.port_contracts_extension extension)) (segment_extension pending extension)

theorem checked_configuration_extension
    (source : CheckedConfiguration operations policy contracts tables world outside scope code stack output demand row)
    (extension : contracts.Extends larger) : CheckedConfiguration operations policy larger tables world outside scope code stack output demand row := by
  cases source with
  | checked source unique evaluated accepted => exact .checked (configuration_extension source extension) unique evaluated accepted

namespace Examples
open OwnerPhaseTransitions (available spend spendAll)
open Ash.OneShot.SharedResumption.NestedExamples
  (contracts inner_known outer_known innerCapture innerBoundary outerCapture outerBoundary outerWaiting resumePlain)
open Ash.OneShot.SharedResumption.Examples (raw effect operations policy tables outside plain operation_known)

def innerRequirements : Requirements [] := .sequence (.request [] raw) (.request [] [])
def innerBoundaryRequirements : Requirements [] := .sequence (.spent 29) (.request [] [])
def outerRequirements : Requirements [29] :=
  .sequence (.invoke ⟨29, .resume⟩ [] (OwnerPhases.ofStack tables innerBoundary)) innerBoundaryRequirements
def outerBoundaryRequirements : Requirements [] := .sequence (.spent 19) (.request [] [])
def innerRecords : Store := [(⟨29, .resume⟩, ⟨[], innerRequirements⟩)]
def records : Store := (⟨19, .resume⟩, ⟨[29], outerRequirements⟩) :: innerRecords
def currentRequirements : Requirements [19, 29] := .sequence (.request [] []) (.invoke ⟨19, .resume⟩ [29] [])
def requirements : Requirements [19, 29] :=
  .sequence (currentRequirements.prepend (OwnerPhases.ofStack tables outerBoundary)) outerBoundaryRequirements

theorem inner_source : Segment operations policy contracts tables [] innerCapture .unit .unit [] innerRequirements [] := by
  have context : Context operations policy contracts [] Environment.empty [effect] .none
      (.perform (Instantiation.freezeEffect effect) 0) .unit .unit [] (.request [] raw) :=
    .perform operation_known List.mem_cons_self (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
  exact .push (.plain (plain := plain) context .none rfl rfl) .nil

theorem inner_boundary_source : Segment operations policy contracts tables [] innerBoundary .unit .unit [] innerBoundaryRequirements innerRecords :=
  .live inner_known rfl rfl ⟨.none, .none⟩ rfl inner_source .nil

theorem outer_source : Segment operations policy contracts tables [] outerCapture .unit .unit [29] outerRequirements innerRecords := by
  have context : Context operations policy contracts [] Environment.empty [effect] (.ticket 8 29) (.resume 8)
      .unit .unit [29] (.invoke ⟨29, .resume⟩ [] []) :=
    .resume inner_known rfl rfl (fun _ member => member)
      (by simp [SharedResumption.NestedExamples.inner, SharedResumption.Examples.contract,
        ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
  exact .push (.plain (plain := resumePlain) context (.bound (Owners.ports_lookup inner_known)) rfl rfl) inner_boundary_source

theorem outer_boundary_source : Segment operations policy contracts tables [] outerBoundary .unit .unit [] outerBoundaryRequirements records :=
  .live outer_known rfl rfl ⟨.none, .none⟩ rfl outer_source .nil

theorem current_source : Expression operations policy contracts [] [effect] (.ticket 7 19) Environment.empty
    (.resume 7 .unit) .unit [19, 29] currentRequirements :=
  .resume outer_known rfl rfl (.stable .unit) (fun _ member => member)
    (by simp [SharedResumption.NestedExamples.outer, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])

theorem configuration_source : Configuration operations policy contracts tables [] (.ticket 7 19) (.resume 7 .unit)
    outerBoundary .unit [19, 29] requirements records :=
  .checked current_source (.bound (Owners.ports_lookup outer_known)) outer_boundary_source

theorem inner_lookup : RecursiveRequirements.lookup ⟨29, .resume⟩ records = some ⟨[], innerRequirements⟩ := rfl
theorem outer_lookup : RecursiveRequirements.lookup ⟨19, .resume⟩ records = some ⟨[29], outerRequirements⟩ := rfl

theorem inner_located : CapturedIn 29 innerCapture outerBoundary := .saved (.push .here)

theorem collected_inner_certified : Certified operations policy contracts tables [] outerBoundary ⟨29, .resume⟩ ⟨[], innerRequirements⟩ :=
  configuration_records configuration_source inner_lookup

theorem collected_outer_certified : Certified operations policy contracts tables [] outerBoundary ⟨19, .resume⟩ ⟨[29], outerRequirements⟩ :=
  configuration_records configuration_source outer_lookup

theorem empty_checked : RecursiveRequirements.Checked records receiving before (.request [] []) [] :=
  .request (by simp [OwnerSource.exportAt, residual_empty])

theorem inner_checked (exported : OwnerSource.exportAt receiving before raw = some row) :
    RecursiveRequirements.Checked records receiving before innerRequirements row := by
  have first : RecursiveRequirements.Checked records receiving before (.request [] raw) row := .request exported
  have result := RecursiveRequirements.Checked.sequence first (empty_checked (receiving := receiving) (before := before))
  simpa only [innerRequirements, List.append_nil] using result

theorem boundary_checked (consumed : before owner = .consumed) :
    RecursiveRequirements.Checked records receiving before (.sequence (.spent owner) (.request [] [])) [] :=
  .sequence (.spent consumed) empty_checked

theorem recursive_check : RecursiveRequirements.Checked records [] (available (ownedTickets outerBoundary)) requirements raw := by
  rw [SharedResumption.NestedExamples.phases_match_runtime.1]
  let initial := available [19, 29]
  let afterOuter := spend initial 19
  let afterInner := spend afterOuter 29
  let caller := OwnerPhases.ofStack tables outerBoundary
  have innermost : RecursiveRequirements.Checked records
      (OwnerPhases.ofStack tables innerBoundary ++ caller) afterInner innerRequirements raw :=
    inner_checked (by decide)
  have innerCall : RecursiveRequirements.Checked records caller afterOuter
      (.invoke ⟨29, .resume⟩ [] (OwnerPhases.ofStack tables innerBoundary)) raw :=
    .invoke inner_lookup (by decide) (OwnerPhases.consumes_complete (by rfl)) innermost
  have innerBoundaryCheck : RecursiveRequirements.Checked records caller (spendAll afterOuter [29]) innerBoundaryRequirements [] :=
    boundary_checked (by decide)
  have outerCheck : RecursiveRequirements.Checked records caller afterOuter outerRequirements raw := by
    have combined := RecursiveRequirements.Checked.sequence innerCall innerBoundaryCheck
    simpa only [outerRequirements, List.append_nil] using combined
  have outerCall : RecursiveRequirements.Checked records caller initial (.invoke ⟨19, .resume⟩ [29] []) raw :=
    .invoke outer_lookup (by decide) (OwnerPhases.consumes_complete (by rfl)) outerCheck
  have currentCheck : RecursiveRequirements.Checked records caller initial currentRequirements raw :=
    .sequence empty_checked outerCall
  have currentPrefixed : RecursiveRequirements.Checked records [] initial (currentRequirements.prepend caller) raw := by
    apply RecursiveRequirements.checked_prepend_iff.mpr
    simpa only [List.append_nil] using currentCheck
  have outerBoundaryCheck : RecursiveRequirements.Checked records [] (spendAll initial [19, 29]) outerBoundaryRequirements [] :=
    boundary_checked (by decide)
  have combined := RecursiveRequirements.Checked.sequence currentPrefixed outerBoundaryCheck
  simpa only [requirements, caller, initial, List.append_nil] using combined

theorem dormant_template_authenticated : Certified operations policy contracts tables [] outerBoundary
    ⟨29, .resume⟩ ⟨[], innerRequirements⟩ := collected_inner_certified

theorem dormant_template_not_callable :
    RecursiveRequirements.evaluate records (OwnerPhases.ofStack tables outerBoundary)
      (available (ownedTickets outerBoundary)) (.invoke ⟨29, .resume⟩ [] []) = none :=
  RecursiveRequirements.invocation_unselectable rfl

theorem derived_evaluation :
    RecursiveRequirements.evaluate records [] (available (ownedTickets outerBoundary)) requirements = some raw :=
  RecursiveRequirements.checked_complete recursive_check

theorem derived_empty_outside_rejected :
    checkResidual [] (RecursiveRequirements.evaluate records [] (available (ownedTickets outerBoundary)) requirements) = false := by
  rw [derived_evaluation]
  decide

theorem checked_configuration : CheckedConfiguration operations policy contracts tables [] outside (.ticket 7 19)
    (.resume 7 .unit) outerBoundary .unit [19, 29] raw :=
  .checked configuration_source (by decide) recursive_check (by decide)

theorem derived_outer_resume : ∃ next : ScopedExecution.Configuration,
    RawStep ⟨.resume 7 .unit, .ticket 7 19, outerBoundary⟩ next [] [.ticket 19] ∧
      OwnerPhaseTransitions.Trace (available (ownedTickets outerBoundary)) [19] (available (ownedTickets next.stack)) := by
  obtain ⟨owner, next, resolved, step, trace⟩ :=
    checked_configuration_resume_progress checked_configuration CallableProtection.Examples.unit_closed
  have same : 19 = owner := Option.some.inj resolved
  cases same
  exact ⟨next, step, trace⟩

theorem derived_ports : ScopedPorts.ConfigurationTyped operations.ports contracts.ports.types []
    ⟨.resume 7 .unit, .ticket 7 19, outerBoundary⟩ .unit := checked_configuration_ports checked_configuration

theorem derived_owners_once : ([19, 29] : List Nat).Nodup := checked_configuration_once checked_configuration

end Examples

end Ash.OneShot.SourceTemplates

#print axioms Ash.OneShot.SourceTemplates.expression_from_source
#print axioms Ash.OneShot.SourceTemplates.expression_value_demand
#print axioms Ash.OneShot.SourceTemplates.expression_ports
#print axioms Ash.OneShot.SourceTemplates.context_from_source
#print axioms Ash.OneShot.SourceTemplates.context_ports
#print axioms Ash.OneShot.SourceTemplates.frame_from_source
#print axioms Ash.OneShot.SourceTemplates.frame_annotations
#print axioms Ash.OneShot.SourceTemplates.frame_ports
#print axioms Ash.OneShot.SourceTemplates.segment_from_source
#print axioms Ash.OneShot.SourceTemplates.segment_ports
#print axioms Ash.OneShot.SourceTemplates.active_capture_located
#print axioms Ash.OneShot.SourceTemplates.active_capture_decompose
#print axioms Ash.OneShot.SourceTemplates.consume_frame
#print axioms Ash.OneShot.SourceTemplates.consume_active_capture
#print axioms Ash.OneShot.SourceTemplates.active_capture_selection
#print axioms Ash.OneShot.SourceTemplates.captured_in_owned
#print axioms Ash.OneShot.SourceTemplates.captured_in_unique
#print axioms Ash.OneShot.SourceTemplates.certified_transport
#print axioms Ash.OneShot.SourceTemplates.records_certified
#print axioms Ash.OneShot.SourceTemplates.lookup_member
#print axioms Ash.OneShot.SourceTemplates.lookup_certified
#print axioms Ash.OneShot.SourceTemplates.certified_selected
#print axioms Ash.OneShot.SourceTemplates.checked_resume_step
#print axioms Ash.OneShot.SourceTemplates.configuration_from_source
#print axioms Ash.OneShot.SourceTemplates.configuration_ports
#print axioms Ash.OneShot.SourceTemplates.configuration_records
#print axioms Ash.OneShot.SourceTemplates.check_configuration
#print axioms Ash.OneShot.SourceTemplates.checked_configuration_ports
#print axioms Ash.OneShot.SourceTemplates.checked_configuration_trace
#print axioms Ash.OneShot.SourceTemplates.checked_configuration_once
#print axioms Ash.OneShot.SourceTemplates.checked_configuration_unique
#print axioms Ash.OneShot.SourceTemplates.checked_configuration_resume_progress
#print axioms Ash.OneShot.SourceTemplates.expression_extension
#print axioms Ash.OneShot.SourceTemplates.context_extension
#print axioms Ash.OneShot.SourceTemplates.frame_extension
#print axioms Ash.OneShot.SourceTemplates.segment_extension
#print axioms Ash.OneShot.SourceTemplates.certified_extension
#print axioms Ash.OneShot.SourceTemplates.configuration_extension
#print axioms Ash.OneShot.SourceTemplates.checked_configuration_extension
#print axioms Ash.OneShot.SourceTemplates.Examples.inner_source
#print axioms Ash.OneShot.SourceTemplates.Examples.inner_boundary_source
#print axioms Ash.OneShot.SourceTemplates.Examples.outer_source
#print axioms Ash.OneShot.SourceTemplates.Examples.outer_boundary_source
#print axioms Ash.OneShot.SourceTemplates.Examples.current_source
#print axioms Ash.OneShot.SourceTemplates.Examples.configuration_source
#print axioms Ash.OneShot.SourceTemplates.Examples.inner_lookup
#print axioms Ash.OneShot.SourceTemplates.Examples.outer_lookup
#print axioms Ash.OneShot.SourceTemplates.Examples.inner_located
#print axioms Ash.OneShot.SourceTemplates.Examples.collected_inner_certified
#print axioms Ash.OneShot.SourceTemplates.Examples.collected_outer_certified
#print axioms Ash.OneShot.SourceTemplates.Examples.empty_checked
#print axioms Ash.OneShot.SourceTemplates.Examples.inner_checked
#print axioms Ash.OneShot.SourceTemplates.Examples.boundary_checked
#print axioms Ash.OneShot.SourceTemplates.Examples.recursive_check
#print axioms Ash.OneShot.SourceTemplates.Examples.dormant_template_authenticated
#print axioms Ash.OneShot.SourceTemplates.Examples.dormant_template_not_callable
#print axioms Ash.OneShot.SourceTemplates.Examples.derived_evaluation
#print axioms Ash.OneShot.SourceTemplates.Examples.derived_empty_outside_rejected
#print axioms Ash.OneShot.SourceTemplates.Examples.checked_configuration
#print axioms Ash.OneShot.SourceTemplates.Examples.derived_outer_resume
#print axioms Ash.OneShot.SourceTemplates.Examples.derived_ports
#print axioms Ash.OneShot.SourceTemplates.Examples.derived_owners_once

#print axioms Ash.OneShot.SourceTemplates.expression_world_weaken
#print axioms Ash.OneShot.SourceTemplates.context_world_weaken
#print axioms Ash.OneShot.SourceTemplates.frame_world_weaken
#print axioms Ash.OneShot.SourceTemplates.segment_world_weaken
#print axioms Ash.OneShot.SourceTemplates.configuration_world_weaken

#print axioms Ash.OneShot.SourceTemplates.clause_modes_substitution
#print axioms Ash.OneShot.SourceTemplates.clause_modes_instantiation
#print axioms Ash.OneShot.SourceTemplates.selected_clause_mode

#print axioms Ash.OneShot.SourceTemplates.value_summary
#print axioms Ash.OneShot.SourceTemplates.ValueSummary.expression
#print axioms Ash.OneShot.SourceTemplates.ValueSummary.ports
#print axioms Ash.OneShot.SourceTemplates.ValueSummary.change_allowed
#print axioms Ash.OneShot.SourceTemplates.ValueSummary.world_weaken
#print axioms Ash.OneShot.SourceTemplates.ValueSummary.extension
