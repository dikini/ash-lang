import CoreCallableGeneralHistory
namespace Ash.OneShot.CoreCallableCallerBarriers
open CoreSyntax CoreMachine CoreTranslation CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreCaptureEntry CoreCallableReachableResume
open CoreCallableSiteLineage CoreCallableGeneralHistory

/-- An immutable actual saved-bind installation. Its suffix is general physical
history, including completions; no flattened cursor is used as an active scope. -/
structure CallerBindPast (graph : Graph) (owners : OwnerMap) (binder : Binder)
    (body : Nat) (environment : CoreMachine.Environment) (plain : PlainData)
    (physical : List CoreMachine.Frame) (target : Stack) where
  predecessor : CoreMachine.State
  site : Nat
  initializer : Nat
  node : CoreSyntax.Node
  known : graph.node site = some node
  kind : node.kind = .bind binder initializer body
  contextCode : Code
  suffixCode : Code
  context : plain.context = .bind binder.id suffixCode
  fuel : Nat
  rawInitializer : Code
  rawBody : Code
  initializerTranslated : translateFuel graph fuel owners initializer = .ok rawInitializer
  bodyTranslated : translateFuel graph fuel owners body = .ok rawBody
  lexical : EnvCloses graph owners predecessor.heap environment
    (.bind binder.id rawInitializer rawBody) (.bind binder.id contextCode suffixCode)
  saved : SavedBindSite graph owners predecessor.heap binder.id body environment plain physical
  originalHistory : GeneralHistory graph predecessor.heap physical target
  actual : CoreMachine.next graph {predecessor with control := .evaluate site environment,frames := physical} =
    .stepped {predecessor with control := .evaluate initializer environment, frames := .bind binder.id body environment :: physical, observations := predecessor.observations ++ [.entered site]}
  focus : RawStep ⟨.bind binder.id contextCode suffixCode,plain.scope,target⟩
    ⟨contextCode,plain.scope,.push (.plain plain) target⟩ [] []

/-- SAME current bind source produces the saved caller receipt and actual
installation; the original full general history remains attached. -/
theorem bind_enter {base : CoreMachine.State}
    (history : GeneralHistory graph base.heap physical target)
    (origin : CurrentScopeOrigin graph owners plain.scope physical)
    (postorder : CoreTranslationFuel.Postorder graph)
    (lineage : SiteLineage graph owners plain.scope site)
    (known : graph.node site = some node) (kind : node.kind = .bind binder initializer body)
    (it : translateFuel graph fuel owners initializer = .ok rawInitializer)
    (bt : translateFuel graph fuel owners body = .ok rawBody)
    (current : EnvCloses graph owners base.heap environment
      (.bind binder.id rawInitializer rawBody) (.bind binder.id initializerCode suffix))
    (notValue : ¬ initializerCode.IsValue) (ready : ClosedExcept binder.id suffix)
    (context : plain.context = .bind binder.id suffix) :
    ∃ past : CallerBindPast graph owners binder body environment plain physical target,
      past.predecessor = base ∧ past.site = site ∧ past.initializer = initializer ∧
      past.contextCode = initializerCode ∧ past.suffixCode = suffix ∧
      HEq past.originalHistory history := by
  obtain ⟨_,saved⟩ := CoreOrdinaryCompletion.bind_components current
  have frame : PlainFrameRel graph owners base.heap (.bind binder.id body environment) plain := by
    change FrameRel graph owners base.heap _ plain.context
    rw [context]
    exact .bind bt saved ready
  have actual : CoreMachine.next graph {base with control := .evaluate site environment,frames := physical} =
    .stepped {base with control := .evaluate initializer environment, frames := .bind binder.id body environment :: physical, observations := base.observations ++ [.entered site]} := by
    cases node with
    | mk original type effects source nodeKind => cases kind; simp only [CoreMachine.next,known]
  have focus : RawStep ⟨.bind binder.id initializerCode suffix,plain.scope,target⟩
    ⟨initializerCode,plain.scope,.push (.plain plain) target⟩ [] [] :=
    .focus plain (by rw [context]; exact .bind notValue) target
  exact ⟨⟨base,site,initializer,node,known,kind,initializerCode,suffix,context,
    fuel,rawInitializer,rawBody,it,bt,current,⟨⟨frame,origin⟩,(bind_sites lineage postorder known kind).2⟩,history,actual,focus⟩,
    rfl,rfl,rfl,rfl,rfl,HEq.rfl⟩

/-- The same immutable bind receipt survives current heap growth. Only current
carriers and history are weakened; its original predecessor is not rewritten. -/
noncomputable def CallerBindPast.current_history
    (past : CallerBindPast graph owners binder body environment plain physical target)
    (extension : HeapExtends past.predecessor.heap heap) :
    GeneralHistory graph heap (.bind binder.id body environment :: physical) (.push (.plain plain) target) :=
  .push (.ordinary (past.saved.saved.related.heap_weaken extension)) (by trivial)
    (past.originalHistory.heap_weaken extension)

/-- An actual beta reset over a current front and that SAME saved-bind barrier.
Repeated literal handler sites inside the reset are permitted. This receipt
records the reset, not a universal claim about future installs or owner misses. -/
structure BetaBindPast (graph : Graph) (callerOwners : OwnerMap) (binder : Binder)
    (body : Nat) (environment : CoreMachine.Environment) (plain : PlainData)
    (physical : List CoreMachine.Frame) (target : Stack)
    (past : CallerBindPast graph callerOwners binder body environment plain physical target)
    (base : CoreMachine.State) (front : List CoreMachine.Frame) (frontTarget : Stack)
    (callOwners : OwnerMap) (parameter calleeBody : Nat) (saved : MEnv)
    (value : MValue) (argumentCode result : Code) (callScope : Execution.Scope) where
  extension : HeapExtends past.predecessor.heap base.heap
  frontHistory : GeneralHistory graph base.heap front frontTarget
  actual : CoreStrictSteps.ApplicationWitness graph callOwners base parameter calleeBody saved value argumentCode result
    (front ++ .bind binder.id body environment :: physical)
    callScope (frontTarget.append (.push (.plain plain) target))
  resetSite : SiteLineage graph [] .none calleeBody

 theorem beta_enter {base : CoreMachine.State}
    (past : CallerBindPast graph callerOwners binder body environment plain physical target)
    (extension : HeapExtends past.predecessor.heap base.heap)
    (frontHistory : GeneralHistory graph base.heap front frontTarget)
    (function : ValueRel graph callOwners base.heap (.closure parameter calleeBody saved) (.lambda parameter result))
    (argument : ValueRel graph callOwners base.heap value argumentCode) (callScope : Execution.Scope) :
    ∃ reset : BetaBindPast graph callerOwners binder body environment plain physical target past base front frontTarget
        callOwners parameter calleeBody saved value argumentCode result callScope,
      reset.frontHistory = frontHistory ∧
      ∃ history : GeneralHistory graph base.heap (front ++ .bind binder.id body environment :: physical)
        (frontTarget.append (.push (.plain plain) target)),
        history = frontHistory.append (CallerBindPast.current_history past extension) := by
  obtain ⟨actual,site⟩ := beta_site function argument
    (front ++ .bind binder.id body environment :: physical) callScope
    (frontTarget.append (.push (.plain plain) target))
  exact ⟨⟨extension,frontHistory,actual,site⟩,rfl,
    frontHistory.append (CallerBindPast.current_history past extension),rfl⟩

/-- Bind return uses the same saved literal site and unchanged original suffix.
It is available only when the actual physical head is this bind frame. -/
theorem bind_return {base : CoreMachine.State}
    (past : CallerBindPast graph owners binder body environment plain physical target)
    (extension : HeapExtends past.predecessor.heap base.heap)
    (argument : ValueRel graph codeOwners base.heap value argumentCode)
    (runtimeScope : Execution.Scope) :
    CoreMachine.next graph {base with control := .returned value,frames := .bind binder.id body environment :: physical} =
      .stepped {base with control := .evaluate body (.binding binder.id value environment),frames := physical} ∧
    RawStep ⟨argumentCode,runtimeScope,.push (.plain plain) target⟩
      ⟨.bind binder.id argumentCode past.suffixCode,plain.scope,target⟩ [] [] ∧
    RawStep ⟨.bind binder.id argumentCode past.suffixCode,plain.scope,target⟩
      ⟨past.suffixCode.subst binder.id argumentCode,plain.scope,target⟩ [] [] ∧
    SiteLineage graph owners plain.scope body ∧
    CurrentScopeOrigin graph owners plain.scope physical ∧
    (∃ history : GeneralHistory graph base.heap physical target,
      history = past.originalHistory.heap_weaken extension) := by
  obtain ⟨fuel,raw,translated,saved,ready⟩ := past.saved.saved.bind_static past.context
  have currentSaved := saved.heap_weaken extension
  obtain ⟨actual,step,_,_⟩ := CoreStrictSteps.bind_complete
    (base := base) translated currentSaved (argument.owner_transport owners) ready physical plain.scope target
  have plug : RawStep ⟨argumentCode,runtimeScope,.push (.plain plain) target⟩
      ⟨.bind binder.id argumentCode past.suffixCode,plain.scope,target⟩ [] [] := by
    simpa only [past.context,Context.plug] using RawStep.plug plain argumentCode argument.closed runtimeScope target
  exact ⟨actual,plug,step,past.saved.site,past.saved.saved.origin,
    past.originalHistory.heap_weaken extension,rfl⟩

/-- The original installation's active caller lineage excludes re-entry of
that caller's own literal handler before any reset/saved-site transition. This
is a local causal miss, not global dynamic pair uniqueness. -/
theorem installed_clause_miss
    (past : GeneralClausePast graph
      (⟨callerHandler,callerOwner,ticket graph callerOwner⟩ :: owners)
      handler owner occurrence dynamicTicket captured data)
    (unique : UniqueHandlerSites graph)
    (active : data.scope = .ticket (ticket graph callerOwner) callerTicket) :
    callerHandler ≠ handler ∨ callerOwner ≠ owner := by
  apply Or.inl
  intro same
  have lineage := past.installation.lineage
  rw [active] at lineage
  apply lineage.not_own_handler unique past.installation.known
  have identity : past.installation.handler = callerHandler := past.sameHandler.trans same.symm
  simpa only [identity] using past.installation.kind

#print axioms bind_enter
#print axioms CallerBindPast.current_history
#print axioms beta_enter
#print axioms bind_return
#print axioms installed_clause_miss
end Ash.OneShot.CoreCallableCallerBarriers
