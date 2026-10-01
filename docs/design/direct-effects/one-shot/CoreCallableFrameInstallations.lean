import CoreCallableSiteLineage
import CoreCallableCleanupOrigins

/-! Past literal installation receipts paired with the existing mapped physical
and target stack. Actual producers retain the original immutable suffix. This
bounded mapped-frame family does not seed arbitrary general chains or cover
projected/disposal cursors. It does not establish future owner lookup misses. -/
namespace Ash.OneShot.CoreCallableFrameInstallations
open CoreSyntax CoreTranslation CoreTranslationFuel CoreMachine
open ScopedExpressions ScopedExecution Instantiation
open CoreValueRelation CoreStrictFrames CoreStrictStack CoreEffectFrames CoreRequestFrames
open CoreCaptureEntry CoreResumeEntry CoreGeneralCaptureResume CoreGeneralStack
open CoreCallableReachableResume CoreCallableCleanupOrigins CoreCallableSiteLineage

structure HandlerPast (graph : Graph) (owners : OwnerMap) (site : Nat)
    (environment : CoreMachine.Environment) (data : HandlerData) where
  predecessor : CoreMachine.State
  originalSuffix : List MappedFrame
  node : CoreSyntax.Node
  handler : Nat
  effect : Effect
  body : Nat
  clauses : List CoreSyntax.Clause
  known : graph.node site = some node
  kind : node.kind = .handler handler effect body clauses
  lineage : SiteLineage graph owners data.scope site
  origin : CurrentScopeOrigin graph owners data.scope (framesOf originalSuffix)
  header : BoundaryRel graph owners predecessor.heap
    (.handlerBoundary site environment data.activation) (.handler data)
  actual : CoreMachine.next graph
    {predecessor with control := .evaluate site environment, frames := framesOf originalSuffix} =
    .stepped {predecessor with control := .evaluate body environment, frames := .handlerBoundary site environment data.activation :: framesOf originalSuffix, nextHandler := predecessor.nextHandler + 1, observations := predecessor.observations ++ [.entered site, .handlerEntered site data.activation]}

structure ClausePast (graph : Graph) (owners : OwnerMap) (handler owner occurrence dynamicTicket : Nat)
    (capturedMaps : List MappedFrame) (data : HandlerData) where
  site : Nat
  environment : CoreMachine.Environment
  installation : HandlerPast graph owners site environment data
  sameHandler : installation.handler = handler
  sameOccurrence : data.activation = occurrence
  selected : CoreSyntax.Clause
  member : selected ∈ installation.clauses
  sameOwner : selected.owner = owner
  predecessor : CoreMachine.State
  insideMaps : List MappedFrame
  outsideMaps : List MappedFrame
  capturedSame : capturedMaps = insideMaps ++ [(owners, .handlerBoundary site environment occurrence)]
  argument : Nat
  value : CoreMachine.Value
  requestEffect : Effect
  operation : Nat
  requestEnvironment : CoreMachine.Environment
  sameTicket : predecessor.nextOwner = dynamicTicket
  actual : CoreMachine.next graph
    (captureBefore predecessor value requestEffect operation requestEnvironment
      (framesOf (insideMaps ++ (owners, .handlerBoundary site environment occurrence) :: outsideMaps))) =
    .stepped (captureAfter predecessor selected argument value handler occurrence site environment
      (framesOf insideMaps) (framesOf outsideMaps))

/-- Ordinary entries require their actual carrier; syntax alone supplies no
frame/value correspondence. Every boundary is paired with full target data. -/
inductive MappedHistory (graph : Graph) (heap : CoreMachine.Heap) : List MappedFrame → Stack → Type where
  | nil : MappedHistory graph heap [] .nil
  | push (frame : PushCarrier graph owners heap core targetFrame)
      (ordinary : match core with | .handlerBoundary _ _ _ => False | _ => True)
      (tail : MappedHistory graph heap maps target) :
      MappedHistory graph heap ((owners, core) :: maps) (.push targetFrame target)
  | handler (installation : HandlerPast graph owners site environment data)
      (header : BoundaryRel graph owners heap (.handlerBoundary site environment data.activation) (.handler data))
      (tail : MappedHistory graph heap maps target) :
      MappedHistory graph heap ((owners, .handlerBoundary site environment data.activation) :: maps)
        (.push (.handler data) target)
  | live (installation : ClausePast graph owners handler owner occurrence dynamicTicket capturedMaps data)
      (header : OwnerHeader graph owners heap handler owner occurrence data)
      (captured : MappedHistory graph heap capturedMaps capturedTarget)
      (tail : MappedHistory graph heap maps target) :
      MappedHistory graph heap
        ((owners, .clauseBoundary handler owner occurrence dynamicTicket (some (framesOf capturedMaps))) :: maps)
        (.live dynamicTicket result data.answer capturedTarget data.scope target)
  | spent (installation : ClausePast graph owners handler owner occurrence dynamicTicket capturedMaps data)
      (header : OwnerHeader graph owners heap handler owner occurrence data)
      (tail : MappedHistory graph heap maps target) :
      MappedHistory graph heap ((owners, .clauseBoundary handler owner occurrence dynamicTicket none) :: maps)
        (.spent dynamicTicket data.answer data.scope target)

theorem MappedHistory.related (history : MappedHistory graph heap maps target) :
    PushedWithMaps graph heap maps target := by
  induction history with
  | nil => exact .nil
  | push frame ordinary tail ih => exact frame.prepend ih
  | handler installation header tail ih => exact .boundary header ih
  | live installation header captured tail ihCaptured ihTail => exact .live header ihCaptured ihTail
  | spent installation header tail ih => exact .spent header ih

noncomputable def MappedHistory.append (front : MappedHistory graph heap frontMaps frontTarget)
    (tail : MappedHistory graph heap suffix tailTarget) :
    MappedHistory graph heap (frontMaps ++ suffix) (frontTarget.append tailTarget) := by
  induction front with
  | nil => exact tail
  | push frame ordinary rest ih => exact .push frame ordinary ih
  | handler installation header rest ih => exact .handler installation header ih
  | live installation header captured rest ihCaptured ih => exact .live installation header captured ih
  | spent installation header rest ih => exact .spent installation header ih

def initial_history (graph : Graph) :
    MappedHistory graph (CoreMachine.initial graph).heap [] .nil := .nil

structure HandlerPick (graph : Graph) (heap : CoreMachine.Heap) (requested : Instance)
    (whole : List MappedFrame) (target : Stack) where
  inside : List MappedFrame
  owners : OwnerMap
  site : Nat
  environment : CoreMachine.Environment
  data : HandlerData
  outside : List MappedFrame
  cap : Stack
  tail : Stack
  installation : HandlerPast graph owners site environment data
  capturedHistory : MappedHistory graph heap (inside ++ [(owners, .handlerBoundary site environment data.activation)]) cap
  outsideHistory : MappedHistory graph heap outside tail
  cut : MappedHandlerCut graph heap requested whole target inside owners site environment data outside cap tail
  shape : whole = inside ++ (owners, .handlerBoundary site environment data.activation) :: outside

noncomputable def handler_pick (history : MappedHistory graph heap whole target)
    (requested : Instance) : Option (HandlerPick graph heap requested whole target) := by
  induction history with
  | nil => exact none
  | @push owners core targetFrame maps target frame ordinary rest ih =>
      by_cases miss : targetFrame.erase.target ≠ some requested
      · cases ih with
        | none => exact none
        | some pick => exact some {
            pick with inside := (owners, core) :: pick.inside
                      cap := .push targetFrame pick.cap
                      capturedHistory := .push frame ordinary pick.capturedHistory
                      cut := .push frame miss pick.cut
                      shape := by simp [pick.shape] }
      · exact none
  | @handler owners site environment data maps target installation header rest ih =>
      by_cases same : data.effectInst = requested
      · exact some {
          inside := [], owners := owners, site := site, environment := environment,
          data := data, outside := maps, cap := .push (.handler data) .nil, tail := target,
          installation := installation,
          capturedHistory := .handler installation header .nil,
          outsideHistory := rest, cut := .hit header same rest.related, shape := rfl }
      · cases ih with
        | none => exact none
        | some pick => exact some {
            pick with inside := (owners, .handlerBoundary site environment data.activation) :: pick.inside
                      cap := .push (.handler data) pick.cap
                      capturedHistory := .handler installation header pick.capturedHistory
                      cut := .push (.boundary header) (by simpa [ExecFrame.erase, HandlerData.erase, Frame.target] using same) pick.cut
                      shape := by simp [pick.shape] }
  | @live owners handler owner occurrence dynamicTicket capturedMaps data capturedTarget maps target result installation header captured rest ihCaptured ih =>
      cases ih with
      | none => exact none
      | some pick => exact some {
          pick with inside := (owners, .clauseBoundary handler owner occurrence dynamicTicket (some (framesOf capturedMaps))) :: pick.inside
                    cap := .live dynamicTicket result data.answer capturedTarget data.scope pick.cap
                    capturedHistory := .live installation header captured pick.capturedHistory
                    cut := .live header captured.related pick.cut
                    shape := by simp [pick.shape] }
  | @spent owners handler owner occurrence dynamicTicket capturedMaps data maps target installation header rest ih =>
      cases ih with
      | none => exact none
      | some pick => exact some {
          pick with inside := (owners, .clauseBoundary handler owner occurrence dynamicTicket none) :: pick.inside
                    cap := .spent dynamicTicket data.answer data.scope pick.cap
                    capturedHistory := .spent installation header pick.capturedHistory
                    cut := .spent header pick.cut
                    shape := by simp [pick.shape] }

structure OwnerPick (graph : Graph) (heap : CoreMachine.Heap) (handler owner : Nat)
    (whole : List MappedFrame) (target : Stack) where
  front : List MappedFrame
  frontTarget : Stack
  owners : OwnerMap
  occurrence : Nat
  dynamicTicket : Nat
  data : HandlerData
  result : Ty
  captured : List MappedFrame
  capturedTarget : Stack
  outside : List MappedFrame
  tail : Stack
  installation : ClausePast graph owners handler owner occurrence dynamicTicket captured data
  header : OwnerHeader graph owners heap handler owner occurrence data
  frontHistory : MappedHistory graph heap front frontTarget
  capturedHistory : MappedHistory graph heap captured capturedTarget
  outsideHistory : MappedHistory graph heap outside tail
  cut : MappedOwnerCut graph heap handler owner whole target front frontTarget owners occurrence dynamicTicket data result captured capturedTarget outside tail

noncomputable def owner_pick (history : MappedHistory graph heap whole target)
    (handler owner : Nat) : Option (OwnerPick graph heap handler owner whole target) := by
  induction history with
  | nil => exact none
  | @push owners core targetFrame maps target frame ordinary rest ih =>
      cases ih with
      | none => exact none
      | some pick => exact some {
          pick with front := (owners, core) :: pick.front
                    frontTarget := .push targetFrame pick.frontTarget
                    frontHistory := .push frame ordinary pick.frontHistory
                    cut := .push frame pick.cut }
  | @handler owners site environment data maps target installation header rest ih =>
      cases ih with
      | none => exact none
      | some pick => exact some {
          pick with front := (owners, .handlerBoundary site environment data.activation) :: pick.front
                    frontTarget := .push (.handler data) pick.frontTarget
                    frontHistory := .handler installation header pick.frontHistory
                    cut := .push (.boundary header) pick.cut }
  | @live owners otherHandler otherOwner occurrence dynamicTicket capturedMaps data capturedTarget maps target result installation header captured rest ihCaptured ih =>
      by_cases same : handler = otherHandler ∧ owner = otherOwner
      · obtain ⟨rfl, rfl⟩ := same
        exact some {
          front := [], frontTarget := .nil, owners := owners,
          occurrence := occurrence, dynamicTicket := dynamicTicket, data := data,
          result := result, captured := capturedMaps, capturedTarget := capturedTarget,
          outside := maps, tail := target, installation := installation, header := header,
          frontHistory := .nil, capturedHistory := captured, outsideHistory := rest,
          cut := .hit header captured.related rest.related }
      · have different : handler ≠ otherHandler ∨ owner ≠ otherOwner := by
          by_cases h : handler = otherHandler
          · exact Or.inr (fun o => same ⟨h,o⟩)
          · exact Or.inl h
        cases ih with
        | none => exact none
        | some pick => exact some {
            pick with front := (owners, .clauseBoundary otherHandler otherOwner occurrence dynamicTicket (some (framesOf capturedMaps))) :: pick.front
                      frontTarget := .live dynamicTicket result data.answer capturedTarget data.scope pick.frontTarget
                      frontHistory := .live installation header captured pick.frontHistory
                      cut := .live header different captured.related pick.cut }
  | @spent owners otherHandler otherOwner occurrence dynamicTicket capturedMaps data maps target installation header rest ih =>
      by_cases same : handler = otherHandler ∧ owner = otherOwner
      · exact none
      · have different : handler ≠ otherHandler ∨ owner ≠ otherOwner := by
          by_cases h : handler = otherHandler
          · exact Or.inr (fun o => same ⟨h,o⟩)
          · exact Or.inl h
        cases ih with
        | none => exact none
        | some pick => exact some {
            pick with front := (owners, .clauseBoundary otherHandler otherOwner occurrence dynamicTicket none) :: pick.front
                      frontTarget := .spent dynamicTicket data.answer data.scope pick.frontTarget
                      frontHistory := .spent installation header pick.frontHistory
                      cut := .spent header different pick.cut }

theorem handler_enter_history {base : CoreMachine.State}
    (postorder : Postorder graph) (lineage : SiteLineage graph owners data.scope site)
    (origin : CurrentScopeOrigin graph owners data.scope (framesOf maps))
    (history : MappedHistory graph base.heap maps target)
    (known : graph.node site = some node) (kind : node.kind = .handler literalHandler effect body clauses)
    (translated : translateFuel graph fuel owners site = .ok (.handle effect rawBody rawClauses))
    (bodyTranslated : translateFuel graph bodyFuel owners body = .ok rawBody)
    (current : EnvCloses graph owners base.heap environment (.handle effect rawBody rawClauses)
      (.handle (freezeEffect data.effectInst) bodyCode data.clauses))
    (activation : data.activation = base.nextHandler) :
    ∃ installation : HandlerPast graph owners site environment data,
      installation.predecessor = base ∧ installation.originalSuffix = maps ∧
      Nonempty (MappedHistory graph base.heap
        ((owners, .handlerBoundary site environment data.activation) :: maps) (.push (.handler data) target)) ∧
      CoreMachine.next graph {base with control := .evaluate site environment, frames := framesOf maps} =
        .stepped {base with control := .evaluate body environment, frames := .handlerBoundary site environment data.activation :: framesOf maps, nextHandler := base.nextHandler + 1, observations := base.observations ++ [.entered site, .handlerEntered site data.activation]} ∧
      RawStep ⟨.handle (freezeEffect data.effectInst) bodyCode data.clauses,data.scope,target⟩
        ⟨bodyCode,data.scope,.push (.handler data) target⟩ [] [] ∧
      SiteLineage graph owners data.scope body := by
  obtain ⟨actual, raw, header, saved, effectSame, bodyTranslation⟩ :=
    CoreEffectEntry.handler_enter known kind translated bodyTranslated current activation (framesOf maps) target
  let installation : HandlerPast graph owners site environment data :=
    ⟨base, maps, node, literalHandler, effect, body, clauses, known, kind, lineage, origin, header, actual⟩
  exact ⟨installation, rfl, rfl, ⟨.handler installation header history⟩, actual, raw,
    lineage.child postorder known (by simp [kind, CoreSyntax.Kind.children])⟩

theorem handler_pick_lookup
    (history : MappedHistory graph heap whole target)
    (picked : handler_pick history requested = some pick) :
    CoreMachine.findInterpreter graph (freezeEffect requested) (framesOf whole) =
      .ok (.handler (framesOf pick.inside) pick.site pick.environment pick.data.activation (framesOf pick.outside)) ∧
    handler_pick history requested = some pick :=
  ⟨pick.cut.realizes.1, picked⟩

theorem owner_pick_lookup
    (history : MappedHistory graph heap whole target)
    (picked : owner_pick history handler owner = some pick) :
    CoreMachine.findOwner handler owner (framesOf whole) =
      .ok ⟨framesOf pick.front,handler,owner,pick.occurrence,pick.dynamicTicket,framesOf pick.captured,framesOf pick.outside⟩ ∧
    owner_pick history handler owner = some pick :=
  ⟨pick.cut.realizes.1, picked⟩

theorem capture_history {base : CoreMachine.State}
    (postorder : Postorder graph) (history : MappedHistory graph base.heap whole target)
    (pick : HandlerPick graph base.heap requested whole target)
    (picked : handler_pick history requested = some pick)
    (selected : pick.installation.clauses.find? (fun clause => clause.operation == operation) = some selectedClause)
    (operand : ValueRel graph operandOwners base.heap value operandCode)
    (requestCarrier : EnvCloses graph operandOwners base.heap requestEnvironment
      (.perform effect operation .unit) (.perform (freezeEffect requested) operation .unit))
    (plain : PlainData) (context : plain.context = .perform (freezeEffect requested) operation)
    (ready : ∀ parameter binder body, ClauseAt operation pick.data.clauses parameter binder body → ClosedExcept parameter body)
    (operationResult : Ty) (runtimeScope : Execution.Scope) :
    ∃ (fuel : Nat) (argument : Binder) (rawBody body : Code),
      selectedClause.argument = .binder argument ∧
      ClauseAt operation pick.data.clauses argument.id (ticket graph selectedClause.owner) body ∧
      translateFuel graph fuel
        (⟨pick.installation.handler,selectedClause.owner,ticket graph selectedClause.owner⟩ :: pick.owners)
        selectedClause.body = .ok rawBody ∧
      EnvCloses graph (⟨pick.installation.handler,selectedClause.owner,ticket graph selectedClause.owner⟩ :: pick.owners)
        base.heap (.binding argument.id value pick.environment) rawBody (body.subst argument.id operandCode) ∧
      GeneralStepWitness graph
        ⟨captureBefore base value effect operation requestEnvironment (framesOf whole),
          .eval ⟨.perform (freezeEffect requested) operation operandCode,plain.scope,target⟩,
          operandOwners,[(operandOwners,.request effect operation requestEnvironment)]⟩
        ⟨captureAfter base selectedClause argument.id value pick.installation.handler pick.data.activation
          pick.site pick.environment (framesOf pick.inside) (framesOf pick.outside),
          .eval ⟨body.subst argument.id operandCode,.ticket (ticket graph selectedClause.owner) base.nextOwner,
            .live base.nextOwner operationResult pick.data.answer pick.cap pick.data.scope pick.tail⟩,
          ⟨pick.installation.handler,selectedClause.owner,ticket graph selectedClause.owner⟩ :: pick.owners,[]⟩ [.ticket base.nextOwner] [] ∧
      (∃ (installation : ClausePast graph pick.owners pick.installation.handler selectedClause.owner
            pick.data.activation base.nextOwner
            (pick.inside ++ [(pick.owners, .handlerBoundary pick.site pick.environment pick.data.activation)]) pick.data)
          (header : OwnerHeader graph pick.owners base.heap pick.installation.handler
            selectedClause.owner pick.data.activation pick.data)
          (successor : MappedHistory graph base.heap
            ((pick.owners, .clauseBoundary pick.installation.handler selectedClause.owner pick.data.activation base.nextOwner
              (some (framesOf (pick.inside ++ [(pick.owners, .handlerBoundary pick.site pick.environment pick.data.activation)])))) :: pick.outside)
            (.live base.nextOwner operationResult pick.data.answer pick.cap pick.data.scope pick.tail)),
        installation.site = pick.site ∧ installation.environment = pick.environment ∧
        HEq installation.installation pick.installation ∧ installation.selected = selectedClause ∧
        successor = .live installation header pick.capturedHistory pick.outsideHistory) ∧
      SiteLineage graph (⟨pick.installation.handler,selectedClause.owner,ticket graph selectedClause.owner⟩ :: pick.owners)
        (.ticket (ticket graph selectedClause.owner) base.nextOwner) selectedClause.body ∧
      handler_pick history requested = some pick := by
  obtain ⟨fuel, argument, rawBody, body, pattern, clauseAt, translated, closed, header, step⟩ :=
    capture_general (GeneralHandlerCut.of_mapped pick.cut) pick.installation.known pick.installation.kind
      selected operand requestCarrier plain context ready operationResult runtimeScope
  let installation : ClausePast graph pick.owners pick.installation.handler selectedClause.owner
      pick.data.activation base.nextOwner
      (pick.inside ++ [(pick.owners, .handlerBoundary pick.site pick.environment pick.data.activation)]) pick.data := {
    site := pick.site, environment := pick.environment, installation := pick.installation,
    sameHandler := rfl, sameOccurrence := rfl, selected := selectedClause,
    member := List.mem_of_find?_eq_some selected, sameOwner := rfl,
    predecessor := base, insideMaps := pick.inside, outsideMaps := pick.outside,
    capturedSame := rfl, argument := argument.id, value := value,
    requestEffect := effect, operation := operation, requestEnvironment := requestEnvironment,
    sameTicket := rfl, actual := by rw [← pick.shape]; exact step.core }
  exact ⟨fuel, argument, rawBody, body, pattern, clauseAt, translated, closed, step,
    ⟨installation, header, .live installation header pick.capturedHistory pick.outsideHistory, rfl, rfl, HEq.rfl, rfl, rfl⟩,
    SiteLineage.selected_clause postorder (CoreCallableCleanupOrigins.CurrentScopeOrigin.canonical pick.installation.origin)
      pick.installation.known pick.installation.kind (List.mem_of_find?_eq_some selected), picked⟩

noncomputable def OwnerPick.restored_history (pick : OwnerPick graph heap handler owner whole target) :
    MappedHistory graph heap
      (pick.captured ++ (pick.front ++ (pick.owners,
        .clauseBoundary handler owner pick.occurrence pick.dynamicTicket none) :: pick.outside))
      (pick.capturedTarget.append
        (pick.frontTarget.append (.spent pick.dynamicTicket pick.data.answer pick.data.scope pick.tail))) :=
  pick.capturedHistory.append (pick.frontHistory.append
    (.spent pick.installation pick.header pick.outsideHistory))

theorem resume_history {base : CoreMachine.State}
    (history : MappedHistory graph base.heap whole target)
    (pick : OwnerPick graph base.heap handler owner whole target)
    (picked : owner_pick history handler owner = some pick)
    (frame : CoreResumeFrames.ResumeRel graph frameOwners base.heap (.resume handler owner) plain)
    (context : plain.context = .resume binder)
    (value : ValueRel graph owners base.heap coreValue code)
    (resolve : plain.scope.resolve binder = some pick.dynamicTicket) (runtimeScope : Execution.Scope) :
    GeneralStepWitness graph
      ⟨resumeBefore base handler owner coreValue (framesOf whole),
        .eval ⟨.resume binder code,plain.scope,target⟩,owners,[(frameOwners,.resume handler owner)]⟩
      ⟨resumeAfter base handler owner pick.occurrence pick.dynamicTicket coreValue
          (framesOf pick.captured) (framesOf pick.front) (framesOf pick.outside),
        .eval ⟨code,plain.scope,pick.capturedTarget.append
          (pick.frontTarget.append (.spent pick.dynamicTicket pick.data.answer pick.data.scope pick.tail))⟩,
        owners,[]⟩ [] [.ticket pick.dynamicTicket] ∧
    (∃ successor : MappedHistory graph base.heap
      (pick.captured ++ (pick.front ++ (pick.owners,
        .clauseBoundary handler owner pick.occurrence pick.dynamicTicket none) :: pick.outside))
      (pick.capturedTarget.append
        (pick.frontTarget.append (.spent pick.dynamicTicket pick.data.answer pick.data.scope pick.tail))),
      successor = pick.restored_history) ∧
    (resumeAfter base handler owner pick.occurrence pick.dynamicTicket coreValue
      (framesOf pick.captured) (framesOf pick.front) (framesOf pick.outside)).frames =
      framesOf (pick.captured ++ (pick.front ++ (pick.owners,
        .clauseBoundary handler owner pick.occurrence pick.dynamicTicket none) :: pick.outside)) ∧
    owner_pick history handler owner = some pick := by
  exact ⟨resume_general (GeneralOwnerCut.of_mapped pick.cut) frame context value resolve runtimeScope,
    ⟨pick.restored_history, rfl⟩,
    by simp [resumeAfter, framesOf, List.map_append, List.append_assoc], picked⟩

theorem HandlerPast.literal_site_unique
    (left : HandlerPast graph leftOwners leftSite leftEnvironment leftData)
    (right : HandlerPast graph rightOwners rightSite rightEnvironment rightData)
    (unique : UniqueHandlerSites graph) (same : left.handler = right.handler) :
    leftSite = rightSite :=
  unique.lookup (rightEffect := right.effect) (rightBody := right.body) (rightClauses := right.clauses)
    left.known left.kind right.known (by simpa only [← same] using right.kind)

/-- This concerns the caller capability at the recorded installation, not all
later dynamic activations. Lambda resets and separately restored sites remain
available, including legitimate repeated literal handlers. -/
theorem HandlerPast.not_caller_reentry
    (receipt : HandlerPast graph
      (⟨callerHandler,callerOwner,ticket graph callerOwner⟩ :: owners) site environment data)
    (unique : UniqueHandlerSites graph)
    (scope : data.scope = .ticket (ticket graph callerOwner) dynamicTicket)
    (same : receipt.handler = callerHandler) : False := by
  have lineage := receipt.lineage
  rw [scope] at lineage
  exact lineage.not_own_handler (effect := receipt.effect) (body := receipt.body) (clauses := receipt.clauses)
    unique receipt.known (by simpa only [same] using receipt.kind)

#print axioms MappedHistory.related
#print axioms MappedHistory.append
#print axioms initial_history
#print axioms handler_pick
#print axioms owner_pick
#print axioms handler_enter_history
#print axioms handler_pick_lookup
#print axioms owner_pick_lookup
#print axioms capture_history
#print axioms OwnerPick.restored_history
#print axioms resume_history
#print axioms HandlerPast.literal_site_unique
#print axioms HandlerPast.not_caller_reentry

end Ash.OneShot.CoreCallableFrameInstallations
