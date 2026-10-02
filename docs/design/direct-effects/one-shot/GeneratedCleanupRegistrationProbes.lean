import CoreCallableGeneratedCleanupRegistration
namespace Ash.OneShot.CoreCallableGeneratedCleanupRegistration.Probes
open CoreCallableGeneratedCleanupRegistration CoreCallableGeneratedChronology
open CoreSyntax CoreTranslation CoreTranslationFuel CoreMachine CoreValueRelation CoreStrictStack CoreStrictFrames
open ScopedExpressions ScopedExecution CoreGeneralStack CoreGeneralCaptureResume CoreGeneralRestoration
open CoreCallableSiteLineage CoreCallableReachableResume CoreCallableCleanupOrigins CoreCallableFrameInstallations
open CoreCallableGeneralHistory CoreCallableRunningOccurrence CoreRequestFrames CoreEffectFrames CoreCleanupFrames

private def graph : Graph := ⟨[
  ⟨0,.unit,[],none,.unit⟩,
  ⟨1,.function .unit .unit [],[],none,.variable 5⟩,
  ⟨2,.unit,[],none,.apply 1 0⟩,
  ⟨3,.unit,[],none,.cleanup ⟨5,.function .unit .unit []⟩ 2 0⟩,
  ⟨4,.unit,[.user 0 []],none,.request (.user 0 []) 0 0⟩,
  ⟨5,.unit,[],none,.handler 0 (.user 0 []) 4 [⟨0,.binder ⟨9,.unit⟩,0,3⟩]⟩,
  ⟨6,.function .unit .unit [],[],none,.function ⟨8,.unit⟩ 0⟩,
  ⟨7,.unit,[],none,.bind ⟨5,.function .unit .unit []⟩ 6 5⟩],7⟩
private def callback : Code := .lambda 8 .unit
private def closure : CoreMachine.Value := .closure 8 0 .empty
private def environment : CoreMachine.Environment := .binding 5 closure .empty
private def registeredEnvironment : CoreMachine.Environment := .binding 9 .unit environment
private def owners : OwnerMap := [⟨0,0,ticket graph 0⟩]
private def clauseCode : Code := .cleanup callback .unit
private def clauses : Clauses := .cons 0 9 (ticket graph 0) clauseCode .nil
private def handlerCode : Code := .handle (.user 0 []) (.perform (.user 0 []) 0 .unit) clauses
private def handlerData : HandlerData := ⟨0,.user 0 [],clauses,.none,.unit,by
  simp [clauses,clauseCode,callback,Clauses.dependencies,Code.dependencies,Syntax.without,Syntax.ticketDependencies]
  ⟩
private def capMaps : List MappedFrame := [([], .handlerBoundary 5 environment 0)]
private def originalMaps : List MappedFrame := [([], .clauseBoundary 0 0 0 0 (some (framesOf capMaps)))]
private def capTarget : Stack := .push (.handler handlerData) .nil
private def originalTarget : Stack := .live 0 .unit .unit capTarget .none .nil
private def active : Execution.Scope := .ticket (ticket graph 0) 0
private def captureBase : CoreMachine.State := {control := .returned .unit,nextHandler := 1}
private def base : CoreMachine.State := captureAfter captureBase ⟨0,.binder ⟨9,.unit⟩,0,3⟩ 9 .unit 0 0 5 environment [] []

private theorem callable : CallableCertificate graph 8 0 .unit := by
  refine ⟨⟨6,⟨8,.unit⟩,_,rfl,rfl,rfl⟩,⟨6,rfl⟩,?_⟩
  intro binder
  simp [Code.dependencies,Syntax.without]
private theorem callback_value : ValueRel graph [] [] closure callback := by
  refine .closure (fuel := 1) (bodyCode := .unit) rfl callable .empty ?_
  simp [callback,ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Code.dependencies,Syntax.without]

private theorem saved_handler : EnvCloses graph [] [] environment
    (.handle (.user 0 []) .unit
      (.cons 0 9 (ticket graph 0) (.cleanup (.variable 5) .unit) .nil)) (.handle (.user 0 []) .unit clauses) := by
  refine .binding callback_value ?_
  simpa [handlerCode,clauses,clauseCode,Code.subst,Clauses.subst] using
    (EnvCloses.empty (graph := graph) (owners := []) (heap := []) (code := .handle (.user 0 []) .unit clauses))

private theorem header : BoundaryRel graph [] [] (.handlerBoundary 5 environment 0) (.handler handlerData) :=
  .handler (graph := graph) (owners := []) (heap := []) (site := 5)
    (node := graph.nodes[5]'(by decide)) (data := handlerData) (environment := environment)
    (fuel := 8) rfl rfl rfl saved_handler
private noncomputable def handlerPast : HandlerPast graph [] 5 environment handlerData := {
  predecessor := {control := .evaluate 5 environment},originalSuffix := []
  node := graph.nodes[5]'(by decide),handler := 0,effect := .user 0 [],body := 4
  clauses := [⟨0,.binder ⟨9,.unit⟩,0,3⟩],known := rfl,kind := rfl
  lineage := .inactive (.empty graph),origin := .inactive (.empty graph),header := header,actual := rfl }
private theorem ownerHeader : OwnerHeader graph [] [] 0 0 0 handlerData :=
  .selected (site := 5) (node := graph.nodes[5]'(by decide)) (clause := ⟨0,.binder ⟨9,.unit⟩,0,3⟩)
    rfl rfl (by simp) rfl header rfl .hit
private noncomputable def clausePast : ClausePast graph [] 0 0 0 0 capMaps handlerData := {
  site := 5,environment := environment,installation := handlerPast,sameHandler := rfl,sameOccurrence := rfl
  selected := ⟨0,.binder ⟨9,.unit⟩,0,3⟩,member := by simp [handlerPast],sameOwner := rfl
  predecessor := captureBase,insideMaps := [],outsideMaps := [],capturedSame := rfl
  argument := 9,value := .unit,requestEffect := .user 0 [],operation := 0,requestEnvironment := environment
  sameTicket := rfl,actual := rfl }
private noncomputable def history : MappedHistory graph [] originalMaps originalTarget :=
  .live clausePast ownerHeader (.handler handlerPast header .nil) .nil

private def action : ActionData := ⟨0,callback,callback_value.closed,active,.unit,[]⟩
private theorem lineage : SiteLineage graph owners action.scope 3 :=
  .clause (.empty graph) (handlerSite := 5) (node := graph.nodes[5]'(by decide)) rfl rfl (by decide)
private theorem current : EnvCloses graph owners [] registeredEnvironment
    (.cleanup (.variable 5) .unit) (.cleanup action.action .unit) := by
  refine .binding (ValueRel.unit (owners := owners)) (.binding (callback_value.owner_transport owners) ?_)
  simpa [Code.subst,action,callback] using
    (EnvCloses.empty (graph := graph) (owners := owners) (heap := []) (code := .cleanup callback .unit))
private theorem ownership : CurrentOwnership graph owners {base with frames := framesOf originalMaps} action.scope originalTarget := by
  constructor
  · intro t
    simp [originalTarget,capTarget,Stack.erase,Control.ticketNames,CoreTicketHistory.capturedTickets,ExecFrame.erase,HandlerData.erase,
      base,captureAfter,captureBase]
  · exact .clause (.empty graph) (.hit [])
private theorem ordered : Postorder graph := checkShape_postorder graph (by rfl)

private theorem registration_produced :
    ∃ _past : RegisteredCleanupPast graph owners base 3 ⟨5,.function .unit .unit []⟩ 2 0 registeredEnvironment action
      (framesOf originalMaps) originalTarget,
      SiteLineage graph owners action.scope 0 ∧ SiteLineage graph owners action.scope 2 ∧
      RawStep ⟨.cleanup action.action .unit,action.scope,originalTarget⟩
        ⟨.unit,action.scope,.push (.armed action) originalTarget⟩ [.cleanup action.identity] [] ∧
      CurrentOwnership graph owners (registeredState base 3 0 2 registeredEnvironment action (framesOf originalMaps))
        action.scope (.push (.armed action) originalTarget) :=
  register_with_sites ordered lineage (node := graph.nodes[3]'(by decide)) rfl rfl rfl
    (fuel := 1) rfl current (parameter := 8) (lambdaBody := .unit) rfl rfl ownership history
private noncomputable def registration := Classical.choose registration_produced
private theorem registration_site : registration.lineage = lineage := Subsingleton.elim _ _

def bodyEnd : CoreMachine.State := {registeredState base 3 0 2 registeredEnvironment action (framesOf originalMaps) with
  control := .returned .unit
  observations := (registeredState base 3 0 2 registeredEnvironment action (framesOf originalMaps)).observations ++ [.entered 0]}
private theorem bodySteps : CoreAllocationHistory.Steps graph 1
    (registeredState base 3 0 2 registeredEnvironment action (framesOf originalMaps)) bodyEnd :=
  .snoc (.refl _) rfl
private theorem bodyBound : TicketBound bodyEnd (.push (.armed action) originalTarget) := by
  intro t
  simp [bodyEnd,registeredState,originalTarget,capTarget,Stack.erase,Control.ticketNames,
    CoreTicketHistory.capturedTickets,ExecFrame.erase,HandlerData.erase,ActionData.erase,base,captureAfter,captureBase]

/-- Actual internal captured configuration, not an initial rich admission proof. -/
theorem active_registration_start :
    ∃ start : RunningStartPast graph owners 2 registeredEnvironment action .unit .unit (framesOf originalMaps) originalTarget,
      StartedFrom registration start 1 ∧
      CoreMachine.next graph bodyEnd = .stepped (started start).state ∧
      Nonempty (Generated start (started start) 0 [] []) ∧
      SiteLineage graph owners .none 2 :=
  start_registered registration bodySteps rfl rfl (ValueRel.unit (owners := owners)) bodyBound

theorem active_original_scope : SiteLineage graph owners active 0 := registration.body_site

theorem active_registration_invocation_steps :
    ∃ start : RunningStartPast graph owners 2 registeredEnvironment action .unit .unit (framesOf originalMaps) originalTarget,
      StartedFrom registration start 1 ∧
      CoreAllocationHistory.Steps graph 3
        {base with control := .evaluate 3 registeredEnvironment,frames := framesOf originalMaps} (started start).state ∧
      start.installed.origin = registration.installed.origin ∧
      (started start).focus.scope = .none ∧ SiteLineage graph owners active 0 := by
  obtain ⟨start,linked,_actual,_generated,_site⟩ := active_registration_start
  have retained := linked.original_and_current_sites registration start
  exact ⟨start,linked,linked.registration_to_invocation registration start,retained.1,retained.2.2.2.2.1,retained.2.1⟩

theorem unique_handler_sites : UniqueHandlerSites graph := checkHandlerSites_sound (by decide)

theorem missing_active_lineage : ¬ SiteLineage graph owners active 5 := by
  intro forbidden
  exact forbidden.not_own_handler unique_handler_sites (node := graph.nodes[5]'(by decide)) rfl rfl

theorem incorrect_registration_node
    (past : RegisteredCleanupPast graph owners base 2 ⟨5,.function .unit .unit []⟩ 2 0 registeredEnvironment action
      (framesOf originalMaps) originalTarget) : False := by
  have actual : graph.node 2 = some (graph.nodes[2]'(by decide)) := rfl
  have same := Option.some.inj (actual.symm.trans past.known)
  have kind := past.kind
  rw [← same] at kind
  cases kind

#print axioms active_registration_start
#print axioms active_original_scope
#print axioms active_registration_invocation_steps
#print axioms unique_handler_sites
#print axioms missing_active_lineage
#print axioms incorrect_registration_node
end Ash.OneShot.CoreCallableGeneratedCleanupRegistration.Probes
