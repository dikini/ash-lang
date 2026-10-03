import CoreCallableRichHandlerFreshness
import CoreCallableRichAdmittedCurrentOrigins

namespace Ash.OneShot.CoreCallableRichHandlerEventConsumers
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreSyntax CoreMachine CoreTranslation CoreTranslationFuel CoreValueRelation CoreStrictStack
open CoreCallableReachableResume CoreCallableCleanupOrigins CoreCallableGeneralHistory
open CoreCallableRunningOccurrence CoreCallableGeneratedChronology
open CoreCallableRichAdmittedCurrentOrigins CoreCallableRichHandlerFreshness
open CoreCallableContractSource (Contract)
open CoreCallableContractAdmission CoreCallableContractExecution
open SourceDeclarationPlans (ClausePlans)
open SourcePlanSignatures (clauseSignatures)
open SourceDependencyChecks.Lexical (ReturnHints)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation (RawTrace)
open SourcePlannedChecks (DeclarationPolicy)

section
variable [DeclarationPolicy]
variable {graph : Graph} {endpoint : Endpoint graph}

omit [DeclarationPolicy] in
/-- The SAME computed actual input has exactly one ordinary handler target edge. -/
theorem handler_transition (input : HandlerInput endpoint) :
    LexicalUnwind.Transition endpoint.point.machine (handler_result input).after.point.machine
      [] [] := by
  have before : endpoint.point.machine =
      .eval ⟨.handle (Instantiation.freezeEffect input.data.effectInst) input.code input.data.clauses,
        input.data.scope,endpoint.lexical⟩ := by
    simp only [Endpoint.point,input.empty.focus,CoreCleanupRunFrames.attach,Stack.append]
  rw [before]
  change LexicalUnwind.Transition
    (.eval ⟨.handle (Instantiation.freezeEffect input.data.effectInst) input.code input.data.clauses,
      input.data.scope,endpoint.lexical⟩)
    (.eval ⟨input.code,input.data.scope,.push (.handler input.data) endpoint.lexical⟩) [] []
  exact .evaluate (.enterHandler input.data input.code endpoint.lexical) (by trivial)

/-- Rich authority and accounting retain the full internally computed handler
and its SAME current body Site, private Families/Plans/Rows and actual input. -/
structure HandlerEvent (nodeId bodyNode : Nat)
    {hints : ReturnHints receiving} {context : Context hints}
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.handle (Instantiation.freezeEffect effect) body arms) runtimeScope endpoint.lexical
      result final context root)
    (current : Current program endpoint site) where
  handler : HandlerData
  residual : List Instance
  table : List (Nat × ClauseContract)
  families : SourceDependencyAnnotations.ClauseDependencies
  plans : ClausePlans handler.clauses families
  rows : ClauseRows (clauseSignatures plans)
  next : Site globals outward world (effect :: residual) actions phases budget ambient
    (installations ++ [endpoint.state.nextHandler]) body runtimeScope
    (.push (.handler handler) endpoint.lexical) result final
    (.handler (effect := effect) (table := table) endpoint.state.nextHandler rows context) root
  input : HandlerInput endpoint
  activation : handler.activation = endpoint.state.nextHandler
  scope : handler.scope = runtimeScope
  effectSame : handler.effectInst = effect
  armsSame : handler.clauses = arms
  frame : HandlerSource globals outward world residual handler result table plans rows
    (actualReceiver world receiving ambient)
  dataSame : input.data = handler
  codeSame : input.code = body
  siteSame : input.site = nodeId
  predecessor : input.installation.predecessor = endpoint.state
  suffix : input.installation.originalSuffix = endpoint.physical
  bodySame : input.installation.body = bodyNode
  after : Current program (handler_result input).after next
  inputSame : after.input = current.input
  past : InstallationsPast program current.input (handler_result input).after next
  transition : LexicalUnwind.Transition current.run.machine after.run.machine [] []
  event : LexicalUnwind.Event current.run after.run
  issued : after.run.issued = current.run.issued
  completed : after.run.completed = current.run.completed
  count : after.eventCount = current.eventCount + 1
  actual : CoreMachine.next graph endpoint.state = .stepped (handler_result input).after.state
  positive : CoreUnwindRelation.Positive endpoint.point.machine (handler_result input).after.point.machine [] []
  matching : Matching graph endpoint (handler_result input).after [] []
  siteOrigins : SiteOrigins (handler_result input).after
  scopeOrigins : EvaluatedScopeOrigins (handler_result input).after

/-- Current handler source/past compute both rich and event successors. No
future Site/Auth/input/result/event/Steps or chosen fresh identity enters. -/
theorem handler_event
    {start : RunningStartPast graph cleanupOwners action originalEnvironment originalData
      savedValue savedCode physical target}
    {hints : ReturnHints receiving} {context : Context hints}
    (ordered : Postorder graph) (run : Generated start endpoint count created discharged)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.handle (Instantiation.freezeEffect effect) body arms) runtimeScope endpoint.lexical
      result final context root)
    (current : Current program endpoint site)
    (control : endpoint.state.control = .evaluate nodeId environment)
    (empty : EmptyFocus endpoint (.handle (Instantiation.freezeEffect effect) body arms) runtimeScope)
    (known : graph.node nodeId = some node)
    (kind : node.kind = .handler binder rawEffect bodyNode rawArms)
    (translated : translateFuel graph fuel endpoint.owners bodyNode = .ok rawBody)
    (siteTranslated : translateFuel graph (fuel + 1) endpoint.owners nodeId =
      .ok (.handle rawEffect rawBody rawClauses))
    (closing : EnvCloses graph endpoint.owners endpoint.state.heap environment
      (.handle rawEffect rawBody rawClauses) (.handle (Instantiation.freezeEffect effect) body arms))
    (past : InstallationsPast program current.input endpoint site) :
    Nonempty (HandlerEvent nodeId bodyNode site current) := by
  obtain ⟨handler,residual,table,families,plans,rows,next,input,
    activation,scope,effectSame,armsSame,frame,dataSame,codeSame,siteSame,predecessor,
    suffix,bodySame,related,actual,matching,siteOrigins,scopeOrigins,nextPast⟩ :=
    handler_preserves_with_past program current.input ordered run site control empty known kind
      translated siteTranslated closing past
  let nextRun : LexicalUnwind.RunState :=
    ⟨(handler_result input).after.point.machine,current.run.issued,current.run.completed⟩
  have transition : LexicalUnwind.Transition current.run.machine nextRun.machine [] [] := by
    change LexicalUnwind.Transition current.run.machine (handler_result input).after.point.machine [] []
    rw [current.machine]
    exact handler_transition input
  have event : LexicalUnwind.Event current.run nextRun := by
    simpa only [List.append_nil,List.nil_append] using
      LexicalUnwind.Event.step transition current.nonallocating_fresh
  let after : Current program (handler_result input).after next := {
    input := current.input,related := related,run := nextRun,machine := rfl,
    eventCount := current.eventCount + 1,past := .step current.past event,
    ledger := LexicalUnwind.event_preserves_ledger event current.ledger }
  exact ⟨⟨handler,residual,table,families,plans,rows,next,input,
    activation,scope,effectSame,armsSame,frame,dataSame,codeSame,siteSame,predecessor,
    suffix,bodySame,after,rfl,nextPast,transition,event,rfl,rfl,rfl,actual,
    .one (handler_transition input),matching,siteOrigins,scopeOrigins⟩⟩

/-- Accounting is the actual appended RawTrace endpoint, separate from full
legacy M4 validity and availability. -/
theorem HandlerEvent.endpoint_accounting
    {hints : ReturnHints receiving} {context : Context hints}
    {site : Site globals outward world allowed actions phases budget ambient installations
      (.handle (Instantiation.freezeEffect effect) body arms) runtimeScope endpoint.lexical
      result final context root}
    {current : Current program endpoint site}
    (event : HandlerEvent nodeId bodyNode site current) :
    Ledger event.after.run.erase ∧ event.after.run.completed.Nodup ∧
      (∀ owner, owner ∈ event.after.run.machine.stack.erase.owners → owner ∉ event.after.run.completed) :=
  event.after.past.ownership ⟨List.Perm.refl [],List.nodup_nil⟩

/-- The computed installation preserves the entire prior causal history. -/
theorem HandlerEvent.full_history
    {rootDemand : List Nat} {root : RecursiveRequirements.Requirements rootDemand}
    {programGlobals : Globals} {programActions : Syntax.UsageTickets}
    {programBudget : Footprint} {programCode : Code}
    {program : CoreCallableInitialAdmission.Program programGlobals programActions programBudget programCode}
    {hints : ReturnHints receiving} {context : Context hints}
    {site : Site globals outward world allowed actions phases budget ambient installations
      (.handle (Instantiation.freezeEffect effect) body arms) runtimeScope endpoint.lexical
      result final context root}
    {current : Current program endpoint site}
    (event : HandlerEvent nodeId bodyNode site current) :
    (handler_result event.input).after.history =
      .handler event.input.installation
        (event.input.installation.header.heap_weaken
          (by rw [event.input.predecessor]; exact fun _ _ h => h))
        endpoint.history :=
  CoreCallableRichHandlerCore.handler_full_history event.input

/-- The SAME runtime transition retains its old physical suffix. -/
theorem HandlerEvent.full_physical
    {hints : ReturnHints receiving} {context : Context hints}
    {site : Site globals outward world allowed actions phases budget ambient installations
      (.handle (Instantiation.freezeEffect effect) body arms) runtimeScope endpoint.lexical
      result final context root}
    {current : Current program endpoint site}
    (event : HandlerEvent nodeId bodyNode site current) :
    (handler_result event.input).after.physical =
      .handlerBoundary event.input.site event.input.environment event.input.data.activation ::
        endpoint.physical := rfl

/-- Actual handler allocation preserves owners, heap and unrelated counters. -/
theorem HandlerEvent.runtime_preserved
    {hints : ReturnHints receiving} {context : Context hints}
    {site : Site globals outward world allowed actions phases budget ambient installations
      (.handle (Instantiation.freezeEffect effect) body arms) runtimeScope endpoint.lexical
      result final context root}
    {current : Current program endpoint site}
    (event : HandlerEvent nodeId bodyNode site current) :
    (handler_result event.input).after.owners = endpoint.owners ∧
    (handler_result event.input).after.state.heap = endpoint.state.heap ∧
    (handler_result event.input).after.state.nextOwner = endpoint.state.nextOwner ∧
    (handler_result event.input).after.state.nextActivation = endpoint.state.nextActivation ∧
    (handler_result event.input).after.state.nextCleanup = endpoint.state.nextCleanup ∧
    (handler_result event.input).after.state.nextClose = endpoint.state.nextClose ∧
    (handler_result event.input).after.state.nextHandler = endpoint.state.nextHandler + 1 ∧
    (handler_result event.input).after.state.observations = endpoint.state.observations ++
      [.entered event.input.site,.handlerEntered event.input.site event.input.data.activation] :=
  CoreCallableRichHandlerCore.handler_runtime_preserved event.input

/-- A different current handler counter cannot describe this actual receipt. -/
theorem HandlerEvent.counter_mismatch
    {hints : ReturnHints receiving} {context : Context hints}
    {site : Site globals outward world allowed actions phases budget ambient installations
      (.handle (Instantiation.freezeEffect effect) body arms) runtimeScope endpoint.lexical
      result final context root}
    {current : Current program endpoint site}
    (event : HandlerEvent nodeId bodyNode site current)
    (different : event.input.data.activation ≠ endpoint.state.nextHandler) : False := by
  apply different
  rw [event.dataSame]
  exact event.activation

/-- A computed positive event cannot have zero historical event increment. -/
theorem HandlerEvent.no_event_rejected
    {hints : ReturnHints receiving} {context : Context hints}
    {site : Site globals outward world allowed actions phases budget ambient installations
      (.handle (Instantiation.freezeEffect effect) body arms) runtimeScope endpoint.lexical
      result final context root}
    {current : Current program endpoint site}
    (event : HandlerEvent nodeId bodyNode site current)
    (same : event.after.eventCount = current.eventCount) : False := by
  have increment := event.count
  omega

/-- This actual allocating Core successor cannot be its own predecessor. -/
theorem HandlerEvent.no_core_identity
    {hints : ReturnHints receiving} {context : Context hints}
    {site : Site globals outward world allowed actions phases budget ambient installations
      (.handle (Instantiation.freezeEffect effect) body arms) runtimeScope endpoint.lexical
      result final context root}
    {current : Current program endpoint site}
    (event : HandlerEvent nodeId bodyNode site current)
    (same : (handler_result event.input).after.state = endpoint.state) : False := by
  have counter := event.runtime_preserved.2.2.2.2.2.2.1
  have unchanged := congrArg CoreMachine.State.nextHandler same
  omega

/-- Current installation membership contradicts the SAME actual past bound. -/
theorem current_counter_membership_rejected
    (current : Current program endpoint
      (site : Site globals outward world allowed actions phases budget ambient installations
        expression runtimeScope stack result final context root))
    (past : InstallationsPast program current.input endpoint site)
    (member : endpoint.state.nextHandler ∈ installations) : False :=
  past.fresh member

end
#print axioms handler_transition
#print axioms handler_event
#print axioms HandlerEvent.endpoint_accounting
#print axioms HandlerEvent.full_history
#print axioms HandlerEvent.full_physical
#print axioms HandlerEvent.runtime_preserved
#print axioms HandlerEvent.counter_mismatch
#print axioms HandlerEvent.no_event_rejected
#print axioms HandlerEvent.no_core_identity
#print axioms current_counter_membership_rejected
end Ash.OneShot.CoreCallableRichHandlerEventConsumers
