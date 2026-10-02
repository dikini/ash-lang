import CoreCallableGeneratedCurrentScopeOrigins
namespace Ash.OneShot.CoreCallableGeneratedBindProducers
open CoreSyntax CoreTranslation CoreTranslationFuel CoreMachine CoreValueRelation CoreStrictStack
open ScopedExpressions ScopedExecution CoreCallableGeneralHistory CoreCallableCallerBarriers
open CoreCallableGeneratedChronology CoreCallableSiteLineage

/-- Literal current bind readiness. The saved caller and current origins are
outputs of the producer, not fields. The physical suffix is unrestricted. -/
structure BindReady (current : Endpoint graph) where
  site : Nat
  binder : Binder
  initializer : Nat
  body : Nat
  environment : Environment
  plain : PlainData
  node : CoreSyntax.Node
  known : graph.node site = some node
  kind : node.kind = .bind binder initializer body
  fuel : Nat
  rawInitializer : Code
  rawBody : Code
  initializerCode : Code
  suffix : Code
  initializerTranslated : translateFuel graph fuel current.owners initializer = .ok rawInitializer
  bodyTranslated : translateFuel graph fuel current.owners body = .ok rawBody
  closing : EnvCloses graph current.owners current.state.heap environment
    (.bind binder.id rawInitializer rawBody) (.bind binder.id initializerCode suffix)
  notValue : ¬ initializerCode.IsValue
  closed : ClosedExcept binder.id suffix
  context : plain.context = .bind binder.id suffix
  control : current.state.control = .evaluate site environment
  empty : EmptyFocus current (.bind binder.id initializerCode suffix) plain.scope

noncomputable def bind_from_current_origins {graph : Graph} {current : Endpoint graph}
    (ordered : Postorder graph) (sites : SiteOrigins current)
    (scopes : EvaluatedScopeOrigins current) (ready : BindReady current) : BindInput current := by
  have lineage : SiteLineage graph current.owners ready.plain.scope ready.site := by
    simpa only [ready.empty.focus] using sites.at ready.control
  have origin : CoreCallableReachableResume.CurrentScopeOrigin graph current.owners ready.plain.scope current.physical := by
    simpa only [ready.empty.focus] using scopes.at ready.control
  let produced := bind_enter current.history origin ordered lineage ready.known ready.kind
      ready.initializerTranslated ready.bodyTranslated ready.closing ready.notValue ready.closed ready.context
  let past := Classical.choose produced
  have equations := Classical.choose_spec produced
  have predecessor := equations.1
  have site := equations.2.1
  have code := equations.2.2.2.1
  have suffix := equations.2.2.2.2.1
  have history := equations.2.2.2.2.2
  exact {
    owners := current.owners
    ownersSame := rfl
    binder := ready.binder
    body := ready.body
    environment := ready.environment
    plain := ready.plain
    past := past
    predecessor := predecessor
    original := history
    control := by rw [site]; exact ready.control
    empty := by rw [code,suffix]; exact ready.empty }

theorem produced_predecessor {graph : Graph} {current : Endpoint graph}
    (ordered : Postorder graph) (sites : SiteOrigins current)
    (scopes : EvaluatedScopeOrigins current) (ready : BindReady current) :
    (bind_from_current_origins ordered sites scopes ready).past.predecessor = current.state :=
  (bind_from_current_origins ordered sites scopes ready).predecessor

theorem produced_history {graph : Graph} {current : Endpoint graph}
    (ordered : Postorder graph) (sites : SiteOrigins current)
    (scopes : EvaluatedScopeOrigins current) (ready : BindReady current) :
    HEq (bind_from_current_origins ordered sites scopes ready).past.originalHistory current.history :=
  (bind_from_current_origins ordered sites scopes ready).original

theorem produced_actual {graph : Graph} {current : Endpoint graph}
    (ordered : Postorder graph) (sites : SiteOrigins current)
    (scopes : EvaluatedScopeOrigins current) (ready : BindReady current) :
    CoreMachine.next graph current.state = .stepped (bind_result (bind_from_current_origins ordered sites scopes ready)).after.state ∧
    Matching graph current (bind_result (bind_from_current_origins ordered sites scopes ready)).after [] [] :=
  Operation.actual (.bind (bind_from_current_origins ordered sites scopes ready))

theorem produced_positive {graph : Graph} {current : Endpoint graph}
    (ordered : Postorder graph) (sites : SiteOrigins current)
    (scopes : EvaluatedScopeOrigins current) (ready : BindReady current) :
    CoreUnwindRelation.Positive current.point.machine
      (bind_result (bind_from_current_origins ordered sites scopes ready)).after.point.machine [] [] := by
  let input := bind_from_current_origins ordered sites scopes ready
  have before : current.point.machine = .eval ⟨.bind input.binder.id input.past.contextCode input.past.suffixCode,input.plain.scope,current.lexical⟩ := by
    simp only [Endpoint.point,input.empty.focus,CoreCleanupRunFrames.attach,Stack.append]
  have after : (bind_result input).after.point.machine =
      .eval ⟨input.past.contextCode,input.plain.scope,.push (.plain input.plain) current.lexical⟩ := by
    simp only [bind_result,Endpoint.point,CoreCleanupRunFrames.attach,Stack.append]
  change CoreUnwindRelation.Positive current.point.machine (bind_result input).after.point.machine [] []
  rw [before,after]
  exact .one (.evaluate input.past.focus (by trivial))

theorem produced_suffix {graph : Graph} {current : Endpoint graph}
    (ordered : Postorder graph) (sites : SiteOrigins current)
    (scopes : EvaluatedScopeOrigins current) (ready : BindReady current) :
    (bind_result (bind_from_current_origins ordered sites scopes ready)).after.physical =
      .bind ready.binder.id ready.body ready.environment :: current.physical := rfl

#print axioms bind_from_current_origins
#print axioms produced_predecessor
#print axioms produced_history
#print axioms produced_actual
#print axioms produced_positive
#print axioms produced_suffix
end Ash.OneShot.CoreCallableGeneratedBindProducers
