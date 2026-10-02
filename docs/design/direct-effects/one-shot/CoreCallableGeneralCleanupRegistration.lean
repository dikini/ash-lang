import CoreCallableGeneralHistory

/-! Actual cleanup registration over SAME complete general history, including
running and retained suffixes. Initial current-site/ownership production and
later saved-anchor activation remain separate obligations. -/
namespace Ash.OneShot.CoreCallableGeneralCleanupRegistration
open CoreSyntax CoreTranslation CoreTranslationFuel CoreMachine CoreValueRelation
open ScopedExpressions ScopedExecution CoreStrictStack CoreStrictFrames CoreCleanupFrames
open CoreGeneralStack CoreGeneralRestoration CoreCallableReachableResume
open CoreCallableCleanupOrigins CoreCallableSiteLineage CoreCallableGeneralHistory

def registeredState (base : CoreMachine.State) (site body action : Nat)
    (environment : CoreMachine.Environment) (data : ActionData) (physical : List CoreMachine.Frame) : CoreMachine.State :=
  {base with control := .evaluate body environment,frames := .cleanupBoundary action environment data.identity :: physical,nextCleanup := base.nextCleanup+1,observations := base.observations ++ [.entered site,.cleanupArmed data.identity]}

structure GeneralRegisteredCleanupPast (graph : Graph) (owners : OwnerMap) (base : CoreMachine.State)
    (site : Nat) (callback : Binder) (action body : Nat) (environment : CoreMachine.Environment)
    (data : ActionData) (physical : List CoreMachine.Frame) (target : Stack) (rawBody bodyCode : Code) where
  node : CoreSyntax.Node
  known : graph.node site = some node
  kind : node.kind = .cleanup callback action body
  postorder : Postorder graph
  lineage : SiteLineage graph owners data.scope site
  identity : data.identity = base.nextCleanup
  installed : SavedCleanupOrigin graph owners base.heap action environment data physical
  history : GeneralHistory graph base.heap physical target
  translated : translateFuel graph (graph.nodes.length+1) owners body = .ok rawBody
  bodyClosing : EnvCloses graph owners base.heap environment rawBody bodyCode
  actual : CoreMachine.next graph {base with control := .evaluate site environment,frames := physical} =
    .stepped (registeredState base site body action environment data physical)

private theorem lambda_is_closure
    (related : ValueRel graph owners heap value (.lambda parameter body)) :
    ∃ parameter body saved, value = .closure parameter body saved := by
  cases related with | closure => exact ⟨_,_,_,rfl⟩

/-- No mapped-frame conversion, supplied successor or successor history. -/
theorem general_register
    (postorder : Postorder graph) (lineage : SiteLineage graph owners data.scope site)
    (known : graph.node site = some node) (kind : node.kind = .cleanup callback action body)
    (shape : checkCleanup graph site callback action = .ok ())
    (translated : translateFuel graph (graph.nodes.length+1) owners body = .ok rawBody)
    (current : EnvCloses graph owners base.heap environment (.cleanup (.variable callback.id) rawBody)
      (.cleanup data.action bodyCode))
    (callable : data.action = .lambda parameter lambdaBody)
    (identity : data.identity = base.nextCleanup)
    (ownership : CurrentOwnership graph owners {base with frames := physical} data.scope target)
    (history : GeneralHistory graph base.heap physical target) :
    ∃ past : GeneralRegisteredCleanupPast graph owners base site callback action body environment data physical target rawBody bodyCode,
      past.history = history ∧
      RawStep ⟨.cleanup data.action bodyCode,data.scope,target⟩
        ⟨bodyCode,data.scope,.push (.armed data) target⟩ [.cleanup data.identity] [] ∧
      CurrentOwnership graph owners (registeredState base site body action environment data physical)
        data.scope (.push (.armed data) target) := by
  obtain ⟨callbackSaved,bodySaved⟩ := cleanup_components current
  obtain ⟨value,lookup,related⟩ := callbackSaved.lookup data.closed
  have closureRelated := related
  rw [callable] at closureRelated
  obtain ⟨parameter,functionBody,captured,rfl⟩ := lambda_is_closure closureRelated
  have delayed := checked_action_translation (owners := owners) shape
  have installed : SavedCleanupOrigin graph owners base.heap action environment data physical :=
    ⟨.armed known kind shape delayed (app_unit callbackSaved) lookup related,ownership.scopeOrigin⟩
  have actual : CoreMachine.next graph {base with control := .evaluate site environment,frames := physical} =
      .stepped (registeredState base site body action environment data physical) := by
    simp [CoreMachine.next,known,kind,lookup,identity,registeredState,List.append_assoc]
  let past : GeneralRegisteredCleanupPast graph owners base site callback action body environment data physical target rawBody bodyCode :=
    ⟨node,known,kind,postorder,lineage,identity,installed,history,translated,bodySaved,actual⟩
  have raw : RawStep ⟨.cleanup data.action bodyCode,data.scope,target⟩
      ⟨bodyCode,data.scope,.push (.armed data) target⟩ [.cleanup data.identity] [] := .enterCleanup data bodyCode target
  have events : CoreTicketHistory.capturedTickets (registeredState base site body action environment data physical).observations =
      CoreTicketHistory.capturedTickets ({base with frames := physical} : CoreMachine.State).observations ++
      issuedTickets [.cleanup data.identity] := by
    simp [registeredState,CoreTicketHistory.capturedTickets,issuedTickets]
  exact ⟨past,rfl,raw,⟨ownership.tickets.step raw events,CurrentScopeOrigin.prepend_cleanup ownership.scopeOrigin⟩⟩

theorem GeneralRegisteredCleanupPast.body_site
    (past : GeneralRegisteredCleanupPast graph owners base site callback action body environment data physical target rawBody bodyCode) :
    SiteLineage graph owners data.scope body :=
  past.lineage.child past.postorder past.known (by simp [past.kind,Kind.children])
theorem GeneralRegisteredCleanupPast.action_site
    (past : GeneralRegisteredCleanupPast graph owners base site callback action body environment data physical target rawBody bodyCode) :
    SiteLineage graph owners data.scope action :=
  past.lineage.child past.postorder past.known (by simp [past.kind,Kind.children])

#print axioms general_register
#print axioms GeneralRegisteredCleanupPast.body_site
#print axioms GeneralRegisteredCleanupPast.action_site
end Ash.OneShot.CoreCallableGeneralCleanupRegistration
