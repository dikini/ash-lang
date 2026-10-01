import CoreCallableFrameInstallations
import CoreCallableCleanupReachableTransport

namespace Ash.OneShot.CoreCallableGeneralHistory
open CoreSyntax CoreTranslation CoreTranslationFuel CoreValueRelation CoreStrictFrames
open CoreStrictStack CoreCaptureEntry CoreResumeEntry
open ScopedExpressions ScopedExecution CoreEffectFrames CoreRequestFrames
open CoreCaptureEntry CoreCleanupFrames CoreCleanupProjection CoreGeneralStack
open CoreGeneralCaptureResume CoreGeneralRestoration CoreCallableCleanupOrigins CoreCallableCleanupReachableTransport
open CoreCallableFrameInstallations CoreCallableReachableResume

/-- Immutable actual installation. Optional maps retain mapped predecessor data
when this general receipt is constructed from the mapped receipt. -/
structure GeneralHandlerPast (graph : Graph) (owners : OwnerMap) (site : Nat)
    (environment : CoreMachine.Environment) (data : HandlerData) where
  predecessor : CoreMachine.State
  originalSuffix : List CoreMachine.Frame
  originalMaps : Option (List MappedFrame)
  mapsSame : ∀ maps, originalMaps = some maps → originalSuffix = framesOf maps
  node : CoreSyntax.Node
  handler : Nat
  effect : Instantiation.Effect
  body : Nat
  clauses : List CoreSyntax.Clause
  known : graph.node site = some node
  kind : node.kind = .handler handler effect body clauses
  lineage : CoreCallableSiteLineage.SiteLineage graph owners data.scope site
  origin : CurrentScopeOrigin graph owners data.scope originalSuffix
  header : BoundaryRel graph owners predecessor.heap
    (.handlerBoundary site environment data.activation) (.handler data)
  actual : CoreMachine.next graph
    {predecessor with control := .evaluate site environment, frames := originalSuffix} =
    .stepped {predecessor with control := .evaluate body environment, frames := .handlerBoundary site environment data.activation :: originalSuffix, nextHandler := predecessor.nextHandler + 1, observations := predecessor.observations ++ [.entered site, .handlerEntered site data.activation]}

def GeneralHandlerPast.from_mapped (past : HandlerPast graph owners site environment data) :
    GeneralHandlerPast graph owners site environment data := {
  predecessor := past.predecessor, originalSuffix := framesOf past.originalSuffix,
  originalMaps := some past.originalSuffix, mapsSame := by intro maps same; cases Option.some.inj same; rfl,
  node := past.node, handler := past.handler, effect := past.effect, body := past.body,
  clauses := past.clauses, known := past.known, kind := past.kind, lineage := past.lineage,
  origin := past.origin, header := past.header, actual := past.actual }

structure GeneralClausePast (graph : Graph) (owners : OwnerMap)
    (handler owner occurrence dynamicTicket : Nat) (capturedPhysical : List CoreMachine.Frame)
    (data : HandlerData) where
  site : Nat
  environment : CoreMachine.Environment
  installation : GeneralHandlerPast graph owners site environment data
  sameHandler : installation.handler = handler
  sameOccurrence : data.activation = occurrence
  selected : CoreSyntax.Clause
  member : selected ∈ installation.clauses
  sameOwner : selected.owner = owner
  predecessor : CoreMachine.State
  originalInside : List CoreMachine.Frame
  originalOutside : List CoreMachine.Frame
  originalCapturedMaps : Option (List MappedFrame)
  originalInsideMaps : Option (List MappedFrame)
  originalOutsideMaps : Option (List MappedFrame)
  insideMapsSame : ∀ maps, originalInsideMaps = some maps → originalInside = framesOf maps
  outsideMapsSame : ∀ maps, originalOutsideMaps = some maps → originalOutside = framesOf maps
  mapsSame : ∀ maps, originalCapturedMaps = some maps → capturedPhysical = framesOf maps
  capturedSame : capturedPhysical = originalInside ++ [.handlerBoundary site environment occurrence]
  argument : Nat
  value : CoreMachine.Value
  requestEffect : Instantiation.Effect
  operation : Nat
  requestEnvironment : CoreMachine.Environment
  sameTicket : predecessor.nextOwner = dynamicTicket
  actual : CoreMachine.next graph
    (captureBefore predecessor value requestEffect operation requestEnvironment
      (originalInside ++ .handlerBoundary site environment occurrence :: originalOutside)) =
    .stepped (captureAfter predecessor selected argument value handler occurrence site environment
      originalInside originalOutside)

def GeneralClausePast.from_mapped
    (past : ClausePast graph owners handler owner occurrence dynamicTicket capturedMaps data) :
    GeneralClausePast graph owners handler owner occurrence dynamicTicket (framesOf capturedMaps) data := {
  site := past.site, environment := past.environment,
  installation := GeneralHandlerPast.from_mapped past.installation, sameHandler := past.sameHandler,
  sameOccurrence := past.sameOccurrence, selected := past.selected, member := past.member,
  sameOwner := past.sameOwner, predecessor := past.predecessor,
  originalInside := framesOf past.insideMaps, originalOutside := framesOf past.outsideMaps,
  originalCapturedMaps := some capturedMaps,
  originalInsideMaps := some past.insideMaps, originalOutsideMaps := some past.outsideMaps,
  insideMapsSame := by intro maps same; cases Option.some.inj same; rfl,
  outsideMapsSame := by intro maps same; cases Option.some.inj same; rfl,
  mapsSame := by intro maps same; cases Option.some.inj same; rfl,
  capturedSame := by simp [past.capturedSame,framesOf,List.map_append],
  argument := past.argument, value := past.value, requestEffect := past.requestEffect,
  operation := past.operation, requestEnvironment := past.requestEnvironment,
  sameTicket := past.sameTicket, actual := by simpa [framesOf,List.map_append] using past.actual }

private theorem push_weaken (frame : PushCarrier graph owners heap core target)
    (extension : HeapExtends heap larger) : PushCarrier graph owners larger core target := by
  cases frame with
  | ordinary frame => exact .ordinary (frame.heap_weaken extension)
  | initializer frame => exact .initializer (frame.heap_weaken extension)
  | request frame => exact .request (frame.heap_weaken extension)
  | resume frame => exact .resume (frame.heap_weaken extension)
  | cleanup frame => exact .cleanup (frame.heap_weaken extension)
  | boundary frame => exact .boundary (frame.heap_weaken extension)

/-- Flattened cursor history retains logical originals without asserting an
active CurrentScopeOrigin on its projected physical suffix. -/
inductive RetainedHistory (graph : Graph) (heap : CoreMachine.Heap) : List CoreMachine.Frame → Stack → Type where
  | nil : RetainedHistory graph heap [] .nil
  | plain (frame : PushCarrier graph owners heap core (.plain plain))
      (tail : RetainedHistory graph heap physical target) :
      RetainedHistory graph heap physical (.push (.plain plain) target)
  | handler (installation : GeneralHandlerPast graph owners site environment data)
      (header : BoundaryRel graph owners heap (.handlerBoundary site environment data.activation) (.handler data))
      (tail : RetainedHistory graph heap physical target) :
      RetainedHistory graph heap physical (.push (.handler data) target)
  | cell (frame : BoundaryRel graph owners heap (.resourceBoundary site key payload) (.cell key payload scope answer))
      (tail : RetainedHistory graph heap physical target) :
      RetainedHistory graph heap (.resourceBoundary site key payload :: physical) (.push (.cell key payload scope answer) target)
  | armed (installed : SavedCleanupOrigin graph owners heap action environment data originalPhysical)
      (tail : RetainedHistory graph heap physical target) :
      RetainedHistory graph heap (.cleanupBoundary action environment data.identity :: physical) (.push (.armed data) target)
  | live (installation : GeneralClausePast graph owners handler owner occurrence dynamicTicket originalCaptured data)
      (header : OwnerHeader graph owners heap handler owner occurrence data)
      (saved : RetainedHistory graph heap savedPhysical savedTarget)
      (tail : RetainedHistory graph heap physical target) :
      RetainedHistory graph heap (savedPhysical ++ physical) (.live dynamicTicket result data.answer savedTarget data.scope target)
  | spent (installation : GeneralClausePast graph owners handler owner occurrence dynamicTicket originalCaptured data)
      (header : OwnerHeader graph owners heap handler owner occurrence data)
      (tail : RetainedHistory graph heap physical target) :
      RetainedHistory graph heap physical (.spent dynamicTicket data.answer data.scope target)
  | retiring (installation : GeneralClausePast graph owners handler owner occurrence dynamicTicket originalCaptured data)
      (header : OwnerHeader graph owners heap handler owner occurrence data)
      (tail : RetainedHistory graph heap physical target) :
      RetainedHistory graph heap physical (.push (.retiring dynamicTicket) target)

theorem RetainedHistory.related (history : RetainedHistory graph heap physical target) :
    RetainedCursor graph heap physical target := by
  induction history with
  | nil => exact .nil
  | plain frame tail ih => exact .plain frame ih
  | handler installation header tail ih => exact .handler header ih
  | cell frame tail ih => exact .cell frame ih
  | armed installed tail ih => exact .armed installed.delayed ih
  | live installation header saved tail ihSaved ihTail => exact .live header ihSaved ihTail
  | spent installation header tail ih => exact .spent header ih
  | retiring installation header tail ih => exact .retiring header ih

noncomputable def RetainedHistory.heap_weaken (history : RetainedHistory graph heap physical target)
    (extension : HeapExtends heap larger) : RetainedHistory graph larger physical target := by
  induction history with
  | nil => exact .nil
  | plain frame tail ih => exact .plain (push_weaken frame extension) ih
  | handler installation header tail ih => exact .handler installation (header.heap_weaken extension) ih
  | cell frame tail ih => exact .cell (frame.heap_weaken extension) ih
  | armed installed tail ih => exact .armed (installed.heap_weaken extension) ih
  | live installation header saved tail ihSaved ihTail => exact .live installation (header.heap_weaken extension) ihSaved ihTail
  | spent installation header tail ih => exact .spent installation (header.heap_weaken extension) ih
  | retiring installation header tail ih => exact .retiring installation (header.heap_weaken extension) ih

private def nonHandler (core : CoreMachine.Frame) : Prop :=
  match core with | .handlerBoundary _ _ _ => False | _ => True

inductive GeneralHistory (graph : Graph) (heap : CoreMachine.Heap) : List CoreMachine.Frame → Stack → Type where
  | nil : GeneralHistory graph heap [] .nil
  | retained (history : RetainedHistory graph heap physical target) : GeneralHistory graph heap physical target
  | push (frame : PushCarrier graph owners heap core target)
      (ordinary : nonHandler core)
      (tail : GeneralHistory graph heap physical lexical) : GeneralHistory graph heap (core :: physical) (.push target lexical)
  | handler (installation : GeneralHandlerPast graph owners site environment data)
      (header : BoundaryRel graph owners heap (.handlerBoundary site environment data.activation) (.handler data))
      (tail : GeneralHistory graph heap physical lexical) :
      GeneralHistory graph heap (.handlerBoundary site environment data.activation :: physical) (.push (.handler data) lexical)
  | running (receipt : RunningReceipt graph owners heap action environment data savedValue savedCode originalPhysical) :
      GeneralHistory graph heap [.cleanupCompletion data.identity savedValue] (.push (.running data savedCode receipt.value.closed) .nil)
  | unwinding (installed : SavedCleanupOrigin graph owners heap action environment data originalPhysical) :
      GeneralHistory graph heap [.cleanupCompletion data.identity .unit] (.push (.unwinding data) .nil)
  | closing (coreIdentity targetIdentity : Nat) (callerScope : Execution.Scope) :
      GeneralHistory graph heap [.closeCompletion coreIdentity] (.push (.closing targetIdentity callerScope) .nil)
  | live (installation : GeneralClausePast graph owners handler owner occurrence dynamicTicket capturedPhysical data)
      (header : OwnerHeader graph owners heap handler owner occurrence data)
      (saved : GeneralHistory graph heap capturedPhysical savedTarget)
      (tail : GeneralHistory graph heap physical target) :
      GeneralHistory graph heap (.clauseBoundary handler owner occurrence dynamicTicket (some capturedPhysical) :: physical)
        (.live dynamicTicket result data.answer savedTarget data.scope target)
  | spent (installation : GeneralClausePast graph owners handler owner occurrence dynamicTicket capturedPhysical data)
      (header : OwnerHeader graph owners heap handler owner occurrence data)
      (tail : GeneralHistory graph heap physical target) :
      GeneralHistory graph heap (.clauseBoundary handler owner occurrence dynamicTicket none :: physical) (.spent dynamicTicket data.answer data.scope target)
  | append (first : GeneralHistory graph heap firstPhysical firstTarget)
      (second : GeneralHistory graph heap secondPhysical secondTarget) :
      GeneralHistory graph heap (firstPhysical ++ secondPhysical) (firstTarget.append secondTarget)

theorem GeneralHistory.related (history : GeneralHistory graph heap physical target) :
    GeneralSegment graph heap physical target := by
  induction history with
  | nil => exact .ordinary .nil
  | retained history => exact .retained history.related
  | push frame ordinary tail ih => exact .push frame ih
  | handler installation header tail ih => exact .push (.boundary header) ih
  | running receipt => exact .completion (.normal receipt.installed.delayed receipt.value)
  | unwinding installed => exact .completion (.unwinding installed.delayed)
  | closing core target scope => exact .completion (.closing core target scope)
  | live installation header saved tail ihSaved ih => exact .live header ihSaved ih
  | spent installation header tail ih => exact .spent header ih
  | append first second ihFirst ihSecond => exact .append ihFirst ihSecond

noncomputable def GeneralHistory.heap_weaken (history : GeneralHistory graph heap physical target)
    (extension : HeapExtends heap larger) : GeneralHistory graph larger physical target := by
  induction history with
  | nil => exact .nil
  | retained history => exact .retained (history.heap_weaken extension)
  | push frame ordinary tail ih => exact .push (push_weaken frame extension) ordinary ih
  | handler installation header tail ih => exact .handler installation (header.heap_weaken extension) ih
  | running receipt => exact .running (receipt.heap_weaken extension)
  | unwinding installed => exact .unwinding (installed.heap_weaken extension)
  | closing core target scope => exact .closing core target scope
  | live installation header saved tail ihSaved ih => exact .live installation (header.heap_weaken extension) ihSaved ih
  | spent installation header tail ih => exact .spent installation (header.heap_weaken extension) ih
  | append first second ihFirst ihSecond => exact .append ihFirst ihSecond

noncomputable def GeneralHistory.of_mapped (history : MappedHistory graph heap maps target) :
    GeneralHistory graph heap (framesOf maps) target := by
  induction history with
  | nil => exact .nil
  | @push owners core targetFrame maps target frame ordinary tail ih =>
    exact .push frame (by cases core <;> simp_all [nonHandler]) ih
  | handler installation header tail ih => exact .handler (GeneralHandlerPast.from_mapped installation) header ih
  | live installation header captured tail ihCaptured ihTail => exact .live (GeneralClausePast.from_mapped installation) header ihCaptured ihTail
  | spent installation header tail ih => exact .spent (GeneralClausePast.from_mapped installation) header ih

theorem GeneralHandlerPast.from_mapped_origin (past : HandlerPast graph owners site environment data) :
    (GeneralHandlerPast.from_mapped past).predecessor = past.predecessor ∧
    (GeneralHandlerPast.from_mapped past).originalMaps = some past.originalSuffix ∧
    (GeneralHandlerPast.from_mapped past).originalSuffix = framesOf past.originalSuffix ∧
    (GeneralHandlerPast.from_mapped past).clauses = past.clauses := ⟨rfl,rfl,rfl,rfl⟩

theorem GeneralClausePast.from_mapped_origin
    (past : ClausePast graph owners handler owner occurrence dynamicTicket capturedMaps data) :
    (GeneralClausePast.from_mapped past).predecessor = past.predecessor ∧
    (GeneralClausePast.from_mapped past).originalCapturedMaps = some capturedMaps ∧
    (GeneralClausePast.from_mapped past).originalInsideMaps = some past.insideMaps ∧
    (GeneralClausePast.from_mapped past).originalOutsideMaps = some past.outsideMaps ∧
    (GeneralClausePast.from_mapped past).selected = past.selected ∧
    (GeneralClausePast.from_mapped past).installation = GeneralHandlerPast.from_mapped past.installation :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Actual handler entry accepts a general suffix, including running cleanup
completions. All original physical data are recorded at this predecessor. -/
theorem handler_enter_history {base : CoreMachine.State}
    (postorder : Postorder graph)
    (lineage : CoreCallableSiteLineage.SiteLineage graph owners data.scope site)
    (origin : CurrentScopeOrigin graph owners data.scope physical)
    (history : GeneralHistory graph base.heap physical target)
    (known : graph.node site = some node) (kind : node.kind = .handler literalHandler effect body clauses)
    (translated : translateFuel graph fuel owners site = .ok (.handle effect rawBody rawClauses))
    (bodyTranslated : translateFuel graph bodyFuel owners body = .ok rawBody)
    (current : EnvCloses graph owners base.heap environment (.handle effect rawBody rawClauses)
      (.handle (Instantiation.freezeEffect data.effectInst) bodyCode data.clauses))
    (activation : data.activation = base.nextHandler) :
    ∃ installation : GeneralHandlerPast graph owners site environment data,
      installation.predecessor = base ∧ installation.originalSuffix = physical ∧
      installation.originalMaps = none ∧
      Nonempty (GeneralHistory graph base.heap
        (.handlerBoundary site environment data.activation :: physical) (.push (.handler data) target)) ∧
      CoreMachine.next graph {base with control := .evaluate site environment, frames := physical} =
        .stepped {base with control := .evaluate body environment, frames := .handlerBoundary site environment data.activation :: physical, nextHandler := base.nextHandler + 1, observations := base.observations ++ [.entered site, .handlerEntered site data.activation]} ∧
      RawStep ⟨.handle (Instantiation.freezeEffect data.effectInst) bodyCode data.clauses,data.scope,target⟩
        ⟨bodyCode,data.scope,.push (.handler data) target⟩ [] [] ∧
      CoreCallableSiteLineage.SiteLineage graph owners data.scope body := by
  obtain ⟨actual,raw,header,saved,effectSame,bodyTranslation⟩ :=
    CoreEffectEntry.handler_enter known kind translated bodyTranslated current activation physical target
  let installation : GeneralHandlerPast graph owners site environment data := {
    predecessor := base, originalSuffix := physical, originalMaps := none,
    mapsSame := (by intro maps same; cases same),
    node := node, handler := literalHandler, effect := effect, body := body,
    clauses := clauses, known := known, kind := kind, lineage := lineage,
    origin := origin, header := header, actual := actual }
  exact ⟨installation,rfl,rfl,rfl,⟨.handler installation header history⟩,actual,raw,
    lineage.child postorder known (by simp [kind,CoreSyntax.Kind.children])⟩

/-- Normal cleanup entry produces the current running occurrence from the same
installed action and original caller value, retaining all outside history. -/
theorem normal_start_history {base : CoreMachine.State}
    (receipt : SavedCleanupOrigin graph cleanupOwners base.heap action environment data physical)
    (saved : ValueRel graph callerOwners base.heap savedValue savedCode)
    (outside : GeneralHistory graph base.heap physical lexical)
    (bounded : TicketBound base (.push (.armed data) lexical)) (scope : Execution.Scope) :
    GeneralStepWitness graph
      ⟨returnedState base savedValue (.cleanupBoundary action environment data.identity :: physical),
        .eval ⟨savedCode,scope,.push (.armed data) lexical⟩,callerOwners,[]⟩
      ⟨startedState base action environment data.identity savedValue physical,
        .eval ⟨.app data.action .unit,.none,.push (.running data savedCode saved.closed) lexical⟩,cleanupOwners,[]⟩ [] [] ∧
    CurrentOwnership graph cleanupOwners
      (startedState base action environment data.identity savedValue physical) .none
      (.push (.running data savedCode saved.closed) lexical) ∧
    ∃ running : RunningReceipt graph cleanupOwners base.heap action environment data savedValue savedCode physical,
      running.installed = receipt ∧
      Nonempty (GeneralHistory graph base.heap (.cleanupCompletion data.identity savedValue :: physical)
        (.push (.running data savedCode saved.closed) lexical)) := by
  obtain ⟨step,current,running⟩ := running_start_owned receipt saved outside.related bounded scope
  exact ⟨step,current,running,rfl,⟨by simpa [Stack.append,startedState] using GeneralHistory.append (.running running) outside⟩⟩

/-- Unit completion consumes the same current running receipt. Its original
suffix is still the actual current suffix here; moved outside origins require
separate history transport, rather than a future-origin assumption. -/
theorem normal_finish_history {base : CoreMachine.State}
    (receipt : RunningReceipt graph cleanupOwners base.heap action environment data savedValue savedCode physical)
    (outside : GeneralHistory graph base.heap physical lexical)
    (bounded : TicketBound base (.push (.running data savedCode receipt.value.closed) lexical))
    (activeOwners : OwnerMap) (scope : Execution.Scope) :
    GeneralStepWitness graph
      ⟨returnedState base .unit (.cleanupCompletion data.identity savedValue :: physical),
        .eval ⟨.unit,scope,.push (.running data savedCode receipt.value.closed) lexical⟩,activeOwners,[]⟩
      ⟨observedState base savedValue physical (.cleanupFinished data.identity),
        .eval ⟨savedCode,data.scope,lexical⟩,cleanupOwners,[]⟩ [] [.cleanup data.identity] ∧
    CurrentOwnership graph cleanupOwners
      (observedState base savedValue physical (.cleanupFinished data.identity)) data.scope lexical ∧
    Nonempty (GeneralHistory graph base.heap physical lexical) := by
  obtain ⟨step,current⟩ := normal_finish_owned receipt.installed receipt.value outside.related bounded activeOwners scope
  exact ⟨step,current,⟨outside⟩⟩

/-- A physical candidate is extracted jointly with its original installation
and both complete current histories, rather than from an arbitrary cut. -/
structure HandlerLocation (graph : Graph) (heap : CoreMachine.Heap)
    (physical : List CoreMachine.Frame) (target : Stack) where
  inside : List CoreMachine.Frame
  front : Stack
  before : GeneralHistory graph heap inside front
  owners : OwnerMap
  site : Nat
  environment : CoreMachine.Environment
  data : HandlerData
  installation : GeneralHandlerPast graph owners site environment data
  header : BoundaryRel graph owners heap (.handlerBoundary site environment data.activation) (.handler data)
  outside : List CoreMachine.Frame
  tail : Stack
  after : GeneralHistory graph heap outside tail
  physicalSame : physical = inside ++ .handlerBoundary site environment data.activation :: outside
  targetSame : target = front.append (.push (.handler data) tail)

noncomputable def HandlerLocation.prepend (location : HandlerLocation graph heap physical target)
    (leading : GeneralHistory graph heap prefixPhysical prefixTarget) :
    HandlerLocation graph heap (prefixPhysical ++ physical) (prefixTarget.append target) := {
  location with inside := prefixPhysical ++ location.inside,
                front := prefixTarget.append location.front,
                before := .append leading location.before,
                physicalSame := by simpa [List.append_assoc] using congrArg (fun xs => prefixPhysical ++ xs) location.physicalSame,
                targetSame := by simpa [stack_append_assoc] using congrArg (fun xs => prefixTarget.append xs) location.targetSame }

noncomputable def HandlerLocation.suffix (location : HandlerLocation graph heap physical target)
    (suffix : GeneralHistory graph heap suffixPhysical suffixTarget) :
    HandlerLocation graph heap (physical ++ suffixPhysical) (target.append suffixTarget) := {
  location with outside := location.outside ++ suffixPhysical,
                tail := location.tail.append suffixTarget,
                after := .append location.after suffix,
                physicalSame := by simpa [List.append_assoc] using congrArg (fun xs => xs ++ suffixPhysical) location.physicalSame,
                targetSame := by simpa [stack_append_assoc,Stack.append] using congrArg (fun xs => xs.append suffixTarget) location.targetSame }

/-- Deterministic physical-handler inventory of this same current history.
Dormant captures and projected logical handlers are not physical candidates. -/
noncomputable def handler_locations (history : GeneralHistory graph heap physical target) :
    List (HandlerLocation graph heap physical target) := by
  induction history with
  | nil => exact []
  | retained history => exact []
  | push frame ordinary tail ih =>
    exact ih.map (fun location => by simpa [Stack.append] using location.prepend (.push frame ordinary .nil))
  | @handler owners site environment data physical lexical installation header tail ih =>
    let here : HandlerLocation graph heap (.handlerBoundary site environment data.activation :: physical)
        (.push (.handler data) lexical) := {
      inside := [],front := .nil,before := .nil,owners := owners,site := site,
      environment := environment,data := data,installation := installation,header := header,
      outside := physical,tail := lexical,after := tail,physicalSame := rfl,targetSame := rfl }
    exact here :: ih.map (fun location => by simpa [Stack.append] using location.prepend (.handler installation header .nil))
  | running receipt => exact []
  | unwinding installed => exact []
  | closing core target scope => exact []
  | live installation header saved tail ihSaved ihTail =>
    exact ihTail.map (fun location => by simpa [Stack.append] using location.prepend (.live installation header saved .nil))
  | spent installation header tail ih =>
    exact ih.map (fun location => by simpa [Stack.append] using location.prepend (.spent installation header .nil))
  | append first second ihFirst ihSecond =>
    exact ihFirst.map (fun location => location.suffix second) ++ ihSecond.map (fun location => location.prepend first)

/-- The location is selected only from this actual history's inventory.
Current route and first physical lookup are checked at that exact location. -/
theorem handler_location_cut (history : GeneralHistory graph heap physical target)
    (index : Fin (handler_locations history).length)
    (same : ((handler_locations history)[index]).data.effectInst = requested)
    (scope : SourceRecursiveRoutes.Scope context ((handler_locations history)[index]).front.erase)
    (route : SourceResourceRoutes.Route outward context requested none)
    (lookup : CoreMachine.findInterpreter graph (Instantiation.freezeEffect requested) physical =
      .ok (.handler ((handler_locations history)[index]).inside ((handler_locations history)[index]).site
        ((handler_locations history)[index]).environment ((handler_locations history)[index]).data.activation
        ((handler_locations history)[index]).outside)) :
    let location := (handler_locations history)[index]
    GeneralHandlerCut graph heap requested physical target location.inside location.owners location.site
      location.environment location.data location.outside
      (location.front.append (.push (.handler location.data) .nil)) location.tail := by
  let location := (handler_locations history)[index]
  exact .split history.related location.before.related location.header same location.after.related
    location.targetSame scope route lookup

/-- Completion capture uses a candidate from the same current history. The
current route and physical lookup select that exact original installation. -/
theorem capture_history {base : CoreMachine.State}
    (history : GeneralHistory graph base.heap physical target)
    (index : Fin (handler_locations history).length) :
    let location := (handler_locations history)[index]
    ∀ (same : location.data.effectInst = requested)
      (prefixScope : SourceRecursiveRoutes.Scope context location.front.erase)
      (route : SourceResourceRoutes.Route outward context requested none)
      (lookup : CoreMachine.findInterpreter graph (Instantiation.freezeEffect requested) physical =
        .ok (.handler location.inside location.site location.environment location.data.activation location.outside))
      (selected : location.installation.clauses.find? (fun clause => clause.operation == operation) = some selectedClause)
      (operand : ValueRel graph operandOwners base.heap value operandCode)
      (requestCarrier : EnvCloses graph operandOwners base.heap requestEnvironment
        (.perform effect operation .unit) (.perform (Instantiation.freezeEffect requested) operation .unit))
      (plain : PlainData) (context : plain.context = .perform (Instantiation.freezeEffect requested) operation)
      (ready : ∀ parameter binder body, ClauseAt operation location.data.clauses parameter binder body → ClosedExcept parameter body)
      (operationResult : Ty) (runtimeScope : Execution.Scope),
    ∃ (fuel : Nat) (argument : Binder) (rawBody body : Code),
      selectedClause.argument = .binder argument ∧
      ClauseAt operation location.data.clauses argument.id (CoreTranslation.ticket graph selectedClause.owner) body ∧
      translateFuel graph fuel
        (⟨location.installation.handler,selectedClause.owner,CoreTranslation.ticket graph selectedClause.owner⟩ :: location.owners)
        selectedClause.body = .ok rawBody ∧
      EnvCloses graph
        (⟨location.installation.handler,selectedClause.owner,CoreTranslation.ticket graph selectedClause.owner⟩ :: location.owners)
        base.heap (.binding argument.id value location.environment) rawBody (body.subst argument.id operandCode) ∧
      GeneralStepWitness graph
        ⟨captureBefore base value effect operation requestEnvironment physical,
          .eval ⟨.perform (Instantiation.freezeEffect requested) operation operandCode,plain.scope,target⟩,
          operandOwners,[(operandOwners,.request effect operation requestEnvironment)]⟩
        ⟨captureAfter base selectedClause argument.id value location.installation.handler location.data.activation
          location.site location.environment location.inside location.outside,
          .eval ⟨body.subst argument.id operandCode,.ticket (CoreTranslation.ticket graph selectedClause.owner) base.nextOwner,
            .live base.nextOwner operationResult location.data.answer
              (location.front.append (.push (.handler location.data) .nil)) location.data.scope location.tail⟩,
          ⟨location.installation.handler,selectedClause.owner,CoreTranslation.ticket graph selectedClause.owner⟩ :: location.owners,[]⟩
          [.ticket base.nextOwner] [] ∧
      ∃ (installation : GeneralClausePast graph location.owners location.installation.handler selectedClause.owner
            location.data.activation base.nextOwner
            (location.inside ++ [.handlerBoundary location.site location.environment location.data.activation]) location.data)
        (header : OwnerHeader graph location.owners base.heap location.installation.handler selectedClause.owner location.data.activation location.data)
        (successor : GeneralHistory graph base.heap
          (.clauseBoundary location.installation.handler selectedClause.owner location.data.activation base.nextOwner
            (some (location.inside ++ [.handlerBoundary location.site location.environment location.data.activation])) :: location.outside)
          (.live base.nextOwner operationResult location.data.answer
            (location.front.append (.push (.handler location.data) .nil)) location.data.scope location.tail)),
        installation.site = location.site ∧ installation.environment = location.environment ∧
        HEq installation.installation location.installation ∧ installation.selected = selectedClause ∧
        installation.originalInside = location.inside ∧ installation.originalOutside = location.outside ∧
        successor = .live installation header
          (.append location.before (.handler location.installation location.header .nil)) location.after := by
  dsimp only
  intro same prefixScope route lookup selected operand requestCarrier plain context ready operationResult runtimeScope
  let location := (handler_locations history)[index]
  have cut := handler_location_cut history index same prefixScope route lookup
  obtain ⟨fuel,argument,rawBody,body,pattern,clauseAt,translated,closed,header,step⟩ :=
    capture_general cut location.installation.known location.installation.kind selected
      operand requestCarrier plain context ready operationResult runtimeScope
  let installation : GeneralClausePast graph location.owners location.installation.handler selectedClause.owner
      location.data.activation base.nextOwner
      (location.inside ++ [.handlerBoundary location.site location.environment location.data.activation]) location.data := {
    site := location.site, environment := location.environment, installation := location.installation,
    sameHandler := rfl, sameOccurrence := rfl, selected := selectedClause,
    member := List.mem_of_find?_eq_some selected, sameOwner := rfl,
    predecessor := base, originalInside := location.inside, originalOutside := location.outside,
    originalCapturedMaps := none, originalInsideMaps := none, originalOutsideMaps := none,
    mapsSame := (by intro maps same; cases same),
    insideMapsSame := (by intro maps same; cases same),
    outsideMapsSame := (by intro maps same; cases same), capturedSame := rfl,
    argument := argument.id, value := value, requestEffect := effect, operation := operation,
    requestEnvironment := requestEnvironment, sameTicket := rfl,
    actual := by simpa only [← location.physicalSame] using step.core }
  let captured := GeneralHistory.append location.before (.handler location.installation location.header .nil)
  exact ⟨fuel,argument,rawBody,body,pattern,clauseAt,translated,closed,step,
    installation,header,.live installation header captured location.after,rfl,rfl,HEq.rfl,rfl,rfl,rfl,rfl⟩

/-- Complete selected owner data come from the same physical live occurrence. -/
structure OwnerLocation (graph : Graph) (heap : CoreMachine.Heap) (handler owner : Nat)
    (physical : List CoreMachine.Frame) (target : Stack) where
  front : List CoreMachine.Frame
  frontTarget : Stack
  frontHistory : GeneralHistory graph heap front frontTarget
  owners : OwnerMap
  occurrence : Nat
  dynamicTicket : Nat
  data : HandlerData
  result : Ty
  captured : List CoreMachine.Frame
  capturedTarget : Stack
  capturedHistory : GeneralHistory graph heap captured capturedTarget
  installation : GeneralClausePast graph owners handler owner occurrence dynamicTicket captured data
  header : OwnerHeader graph owners heap handler owner occurrence data
  outside : List CoreMachine.Frame
  tail : Stack
  outsideHistory : GeneralHistory graph heap outside tail
  whole : GeneralHistory graph heap physical target
  physicalSame : physical = front ++ .clauseBoundary handler owner occurrence dynamicTicket (some captured) :: outside
  targetSame : target = frontTarget.append (.live dynamicTicket result data.answer capturedTarget data.scope tail)
  cut : GeneralOwnerCut graph heap handler owner physical target front frontTarget owners occurrence dynamicTicket
    data result captured capturedTarget outside tail

private abbrev OwnerPass (handler owner : Nat) (physical : List CoreMachine.Frame) : Prop :=
  ∀ rest cut, CoreMachine.findOwner handler owner rest = .ok cut →
    CoreMachine.findOwner handler owner (physical ++ rest) = .ok {cut with inside := physical ++ cut.inside}

noncomputable def OwnerLocation.prepend (location : OwnerLocation graph heap handler owner physical target)
    (leading : GeneralHistory graph heap leadingPhysical leadingTarget)
    (pass : OwnerPass handler owner leadingPhysical) :
    OwnerLocation graph heap handler owner (leadingPhysical ++ physical) (leadingTarget.append target) := by
  have targetSame : leadingTarget.append target =
      (leadingTarget.append location.frontTarget).append (.live location.dynamicTicket location.result location.data.answer location.capturedTarget location.data.scope location.tail) :=
    by simpa [stack_append_assoc] using congrArg (fun xs => leadingTarget.append xs) location.targetSame
  exact {
    location with front := leadingPhysical ++ location.front,
                  frontTarget := leadingTarget.append location.frontTarget,
                  frontHistory := .append leading location.frontHistory,
                  whole := .append leading location.whole,
                  physicalSame := by simpa [List.append_assoc] using congrArg (fun xs => leadingPhysical ++ xs) location.physicalSame,
                  targetSame := targetSame,
                  cut := .split (GeneralHistory.append leading location.whole).related (GeneralHistory.append leading location.frontHistory).related
                    location.header location.capturedHistory.related location.outsideHistory.related targetSame
                    (pass _ _ location.cut.realizes.1) }

noncomputable def OwnerLocation.suffix (location : OwnerLocation graph heap handler owner physical target)
    (suffix : GeneralHistory graph heap suffixPhysical suffixTarget) :
    OwnerLocation graph heap handler owner (physical ++ suffixPhysical) (target.append suffixTarget) := by
  have targetSame : target.append suffixTarget =
      location.frontTarget.append (.live location.dynamicTicket location.result location.data.answer location.capturedTarget location.data.scope (location.tail.append suffixTarget)) :=
    by simpa [stack_append_assoc,Stack.append] using congrArg (fun xs => xs.append suffixTarget) location.targetSame
  exact {
    location with outside := location.outside ++ suffixPhysical,
                  tail := location.tail.append suffixTarget,
                  outsideHistory := .append location.outsideHistory suffix,
                  whole := .append location.whole suffix,
                  physicalSame := by simpa [List.append_assoc] using congrArg (fun xs => xs ++ suffixPhysical) location.physicalSame,
                  targetSame := targetSame,
                  cut := .split (GeneralHistory.append location.whole suffix).related location.frontHistory.related
                    location.header location.capturedHistory.related (GeneralHistory.append location.outsideHistory suffix).related targetSame
                    (CoreSuffixSplice.owner_append location.cut.realizes.1 suffixPhysical) }

/-- Missing prefixes carry a derived physical traversal law. Blocked means the
nearest matching physical occurrence was spent; append must not search past it. -/
inductive OwnerSearch (graph : Graph) (heap : CoreMachine.Heap) (handler owner : Nat)
    (physical : List CoreMachine.Frame) (target : Stack) : Type where
  | found (location : OwnerLocation graph heap handler owner physical target)
  | missing (pass : OwnerPass handler owner physical)
  | blocked

noncomputable def OwnerSearch.prepend (search : OwnerSearch graph heap handler owner physical target)
    (leading : GeneralHistory graph heap leadingPhysical leadingTarget)
    (pass : OwnerPass handler owner leadingPhysical) :
    OwnerSearch graph heap handler owner (leadingPhysical ++ physical) (leadingTarget.append target) := by
  cases search with
  | found location => exact .found (location.prepend leading pass)
  | blocked => exact .blocked
  | missing restPass =>
    exact .missing (by intro rest cut found; simpa [List.append_assoc] using pass _ _ (restPass _ _ found))

private theorem push_owner_pass (frame : PushCarrier graph owners heap core target)
    (found : CoreMachine.findOwner handler owner rest = .ok cut) :
    CoreMachine.findOwner handler owner (core :: rest) = .ok {cut with inside := core :: cut.inside} := by
  cases frame with
  | ordinary related =>
      rename_i plain
      change CoreStrictFrames.FrameRel graph owners heap core plain.context at related
      generalize contextEq : plain.context = context at related
      cases related <;> simp [CoreMachine.findOwner,found,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | initializer related => cases related; simp [CoreMachine.findOwner,found,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | request related => cases related; simp [CoreMachine.findOwner,found,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | resume related => cases related; simp [CoreMachine.findOwner,found,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | cleanup related => cases related; simp [CoreMachine.findOwner,found,Bind.bind,Except.bind,Pure.pure,Except.pure]
  | boundary related => cases related <;> simp [CoreMachine.findOwner,found,Bind.bind,Except.bind,Pure.pure,Except.pure]

noncomputable def owner_search (history : GeneralHistory graph heap physical target) (handler owner : Nat) :
    OwnerSearch graph heap handler owner physical target := by
  cases history with
  | nil => exact .missing (by intro rest cut found; exact found)
  | retained history => exact .missing (fun rest cut found => CoreGeneralStack.RetainedCursor.owner_lookup_pass history.related found)
  | @push owners core frameTarget physical lexical frame ordinary tail =>
    have pass : OwnerPass handler owner [core] := by
      intro rest cut found
      simpa using push_owner_pass frame found
    simpa [Stack.append] using (owner_search tail handler owner).prepend (.push frame ordinary .nil) pass
  | @handler owners site environment data physical lexical installation header tail =>
    have pass : OwnerPass handler owner [.handlerBoundary site environment data.activation] := by
      intro rest cut found
      simpa using push_owner_pass (PushCarrier.boundary header) found
    simpa [Stack.append] using (owner_search tail handler owner).prepend (.handler installation header .nil) pass
  | running receipt => exact .missing (by intro rest cut found; simpa using (CompletionRel.normal receipt.installed.delayed receipt.value).owner_pass found)
  | unwinding installed => exact .missing (by intro rest cut found; simpa using (CompletionRel.unwinding installed.delayed).owner_pass found)
  | closing core target scope => exact .missing (by intro rest cut found; simpa using (CompletionRel.closing (graph := graph) (heap := heap) core target scope).owner_pass found)
  | @live owners otherHandler otherOwner occurrence dynamicTicket captured data capturedTarget physical target result installation header saved tail =>
    by_cases same : handler = otherHandler ∧ owner = otherOwner
    · obtain ⟨rfl,rfl⟩ := same
      exact .found {
        front := [],frontTarget := .nil,frontHistory := .nil,owners := owners,
        occurrence := occurrence,dynamicTicket := dynamicTicket,data := data,result := result,
        captured := captured,capturedTarget := capturedTarget,capturedHistory := saved,
        installation := installation,header := header,outside := physical,tail := target,
        outsideHistory := tail,whole := .live installation header saved tail,
        physicalSame := rfl,targetSame := rfl,cut := .hit header saved.related tail.related }
    · have pass : OwnerPass handler owner [.clauseBoundary otherHandler otherOwner occurrence dynamicTicket (some captured)] := by
        intro rest cut found
        simp [CoreMachine.findOwner,Bool.and_eq_true,beq_iff_eq,same,found,Functor.map,Except.map]
      simpa [Stack.append] using (owner_search tail handler owner).prepend (.live installation header saved .nil) pass
  | @spent owners otherHandler otherOwner occurrence dynamicTicket captured data physical target installation header tail =>
    by_cases same : handler = otherHandler ∧ owner = otherOwner
    · exact .blocked
    · have pass : OwnerPass handler owner [.clauseBoundary otherHandler otherOwner occurrence dynamicTicket none] := by
        intro rest cut found
        simp [CoreMachine.findOwner,Bool.and_eq_true,beq_iff_eq,same,found,Functor.map,Except.map]
      simpa [Stack.append] using (owner_search tail handler owner).prepend (.spent installation header .nil) pass
  | append first second =>
    cases owner_search first handler owner with
    | found location => exact .found (location.suffix second)
    | blocked => exact .blocked
    | missing pass => exact (owner_search second handler owner).prepend first pass
termination_by structural history

theorem owner_search_lookup
    (history : GeneralHistory graph heap physical target)
    (picked : owner_search history handler owner = .found location) :
    CoreMachine.findOwner handler owner physical =
      .ok ⟨location.front,handler,owner,location.occurrence,location.dynamicTicket,location.captured,location.outside⟩ ∧
    owner_search history handler owner = .found location := ⟨location.cut.realizes.1,picked⟩

noncomputable def OwnerLocation.restored_history (location : OwnerLocation graph heap handler owner physical target) :
    GeneralHistory graph heap
      (location.captured ++ (location.front ++
        .clauseBoundary handler owner location.occurrence location.dynamicTicket none :: location.outside))
      (location.capturedTarget.append (location.frontTarget.append
        (.spent location.dynamicTicket location.data.answer location.data.scope location.tail))) :=
  location.capturedHistory.append (location.frontHistory.append
    (.spent location.installation location.header location.outsideHistory))

/-- Actual resume consumes the owner selected by this same current history.
The original capture, arbitrary current front and selected receipt survive in
that exact order; only the selected physical live marker becomes spent. -/
theorem resume_history {base : CoreMachine.State}
    (history : GeneralHistory graph base.heap physical target)
    {location : OwnerLocation graph base.heap handler owner physical target}
    (picked : owner_search history handler owner = .found location)
    (frame : CoreResumeFrames.ResumeRel graph frameOwners base.heap (.resume handler owner) plain)
    (context : plain.context = .resume binder)
    (value : ValueRel graph owners base.heap coreValue code)
    (resolve : plain.scope.resolve binder = some location.dynamicTicket) (runtimeScope : Execution.Scope) :
    GeneralStepWitness graph
      ⟨resumeBefore base handler owner coreValue physical,
        .eval ⟨.resume binder code,plain.scope,target⟩,owners,[(frameOwners,.resume handler owner)]⟩
      ⟨resumeAfter base handler owner location.occurrence location.dynamicTicket coreValue
          location.captured location.front location.outside,
        .eval ⟨code,plain.scope,location.capturedTarget.append (location.frontTarget.append
          (.spent location.dynamicTicket location.data.answer location.data.scope location.tail))⟩,owners,[]⟩
        [] [.ticket location.dynamicTicket] ∧
    (∃ successor : GeneralHistory graph base.heap
      (location.captured ++ (location.front ++
        .clauseBoundary handler owner location.occurrence location.dynamicTicket none :: location.outside))
      (location.capturedTarget.append (location.frontTarget.append
        (.spent location.dynamicTicket location.data.answer location.data.scope location.tail))),
      successor = location.restored_history) ∧
    (resumeAfter base handler owner location.occurrence location.dynamicTicket coreValue
      location.captured location.front location.outside).frames =
      location.captured ++ (location.front ++
        .clauseBoundary handler owner location.occurrence location.dynamicTicket none :: location.outside) ∧
    owner_search history handler owner = .found location := by
  exact ⟨resume_general location.cut frame context value resolve runtimeScope,
    ⟨location.restored_history,rfl⟩,by simp [resumeAfter,List.append_assoc],picked⟩

/-- A matching spent occurrence is never skipped to an older activation. -/
theorem owner_search_spent
    (installation : GeneralClausePast graph owners handler owner occurrence dynamicTicket captured data)
    (header : OwnerHeader graph owners heap handler owner occurrence data)
    (tail : GeneralHistory graph heap physical target) :
    owner_search (.spent installation header tail) handler owner = .blocked := by
  simp [owner_search]

#print axioms GeneralHandlerPast.from_mapped
#print axioms GeneralClausePast.from_mapped
#print axioms RetainedHistory.related
#print axioms RetainedHistory.heap_weaken
#print axioms GeneralHistory.related
#print axioms GeneralHistory.heap_weaken
#print axioms GeneralHistory.of_mapped
#print axioms GeneralHandlerPast.from_mapped_origin
#print axioms GeneralClausePast.from_mapped_origin
#print axioms handler_enter_history
#print axioms normal_start_history
#print axioms normal_finish_history
#print axioms HandlerLocation.prepend
#print axioms HandlerLocation.suffix
#print axioms handler_locations
#print axioms handler_location_cut
#print axioms capture_history
#print axioms OwnerLocation.prepend
#print axioms OwnerLocation.suffix
#print axioms OwnerSearch.prepend
#print axioms owner_search
#print axioms owner_search_lookup
#print axioms OwnerLocation.restored_history
#print axioms resume_history
#print axioms owner_search_spent
end Ash.OneShot.CoreCallableGeneralHistory
