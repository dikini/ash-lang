import CoreCallableHandlerPastOrigins
import CoreCallableRichHandlerCore
import CoreCallableRichAdmittedCurrentOrigins

namespace Ash.OneShot.CoreCallableRichHandlerFreshness
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreSyntax CoreMachine CoreTranslation CoreTranslationFuel CoreValueRelation CoreStrictStack
open CoreCallableReachableResume CoreCallableCleanupOrigins CoreCallableGeneralHistory
open CoreCallableRunningOccurrence CoreCallableGeneratedChronology
open CoreCallableContractSource (Contract)
open CoreCallableContractAdmission CoreCallableContractExecution
open CoreCallableInitialAdmission CoreCallableInitialChronology
open SourceDeclarationPlans (ClausePlans)
open SourcePlanSignatures (clauseSignatures)
open SourceDependencyChecks.Lexical (ReturnHints)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (DeclarationPolicy)

section
variable [DeclarationPolicy]

/-- Only two missing actual-past facts accompany the EXISTING full Site. The
original accepted Program/Input remain indexed; no Source or Current is copied. -/
structure InstallationsPast
    (program : Program originalGlobals originalActions originalBudget originalCode)
    (input : InitialInput graph originalCode) (endpoint : Endpoint graph)
    (_site : Site globals outward world allowed actions phases budget ambient installations
      expression runtimeScope stack result final context root) : Prop where
  actual : ∃ count, CoreAllocationHistory.Steps graph count (CoreMachine.initial graph) endpoint.state
  membership : installations ⊆ CoreHandlerHistory.enteredHandlers endpoint.state.observations

/-- All accepted Programs with SAME executed InitialInput start with no past
installations. This delegates to the existing initial endpoint and full Site. -/
theorem initial_past
    (program : Program globals actions budget code) (input : InitialInput graph code) :
    InstallationsPast program input (initial_endpoint input) program.site :=
  ⟨⟨0, .refl _⟩, by simp [initial_endpoint, CoreMachine.initial, CoreHandlerHistory.enteredHandlers]⟩

/-- The actual original-root Core past computes its current counter history. -/
theorem InstallationsPast.history
    (past : InstallationsPast program initialInput endpoint site) :
    CoreHandlerHistory.History endpoint.state := by
  obtain ⟨count,steps⟩ := past.actual
  exact CoreHandlerHistory.initial_steps_history _ steps

/-- Current absence is derived, not an input or selected fresh replacement. -/
theorem InstallationsPast.fresh
    (past : InstallationsPast program initialInput endpoint
      (site : Site globals outward world allowed actions phases budget ambient installations
        expression runtimeScope stack result final context root)) :
    endpoint.state.nextHandler ∉ installations :=
  CoreHandlerHistory.current_counter_not_member _ past.history _ past.membership

/-- Pure actual-past transport covers all thirteen named operations. It outputs
only historical facts; no rich future Site/Auth or successful-step seed enters. -/
theorem InstallationsPast.operation
    {graph : Graph} {before after : Endpoint graph}
    {program : Program originalGlobals originalActions originalBudget originalCode}
    {initialInput : InitialInput graph originalCode}
    (past : InstallationsPast program initialInput before
      (site : Site globals outward world allowed actions phases budget ambient installations
        expression runtimeScope stack result final context root))
    (operation : Operation before after created discharged) :
    (∃ count, CoreAllocationHistory.Steps graph count (CoreMachine.initial graph) after.state) ∧
    (installations ++ CoreCallableHandlerPastOrigins.Operation.added_handlers operation) ⊆
      CoreHandlerHistory.enteredHandlers after.state.observations := by
  obtain ⟨count,steps⟩ := past.actual
  refine ⟨⟨count+1,.snoc steps operation.actual.1⟩,?_⟩
  rw [(CoreCallableHandlerPastOrigins.Operation.handler_projection operation).2]
  intro identity member
  rcases List.mem_append.mp member with old | added
  · exact List.mem_append_left _ (past.membership old)
  · exact List.mem_append_right _ added

/-- Internal freshness calls the unchanged full handler consumer and computes
its SAME rich successor and original-root past witness. -/
theorem handler_preserves_with_past
    {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action originalEnvironment originalData
      savedValue savedCode physical target}
    {endpoint : Endpoint graph} {hints : ReturnHints receiving} {context : Context hints}
    (program : Program originalGlobals originalActions originalBudget originalCode)
    (initialInput : InitialInput graph originalCode)
    (ordered : Postorder graph) (run : Generated start endpoint count created discharged)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.handle (Instantiation.freezeEffect effect) body arms) runtimeScope endpoint.lexical
      result final context root)
    (control : endpoint.state.control = .evaluate nodeId environment)
    (empty : EmptyFocus endpoint (.handle (Instantiation.freezeEffect effect) body arms) runtimeScope)
    (known : graph.node nodeId = some node)
    (kind : node.kind = .handler binder rawEffect bodyNode rawArms)
    (translated : translateFuel graph fuel endpoint.owners bodyNode = .ok rawBody)
    (siteTranslated : translateFuel graph (fuel + 1) endpoint.owners nodeId =
      .ok (.handle rawEffect rawBody rawClauses))
    (closing : EnvCloses graph endpoint.owners endpoint.state.heap environment
      (.handle rawEffect rawBody rawClauses) (.handle (Instantiation.freezeEffect effect) body arms))
    (past : InstallationsPast program initialInput endpoint site) :
    ∃ handler : HandlerData, ∃ residual : List Instance, ∃ table : List (Nat × ClauseContract),
    ∃ families : SourceDependencyAnnotations.ClauseDependencies,
    ∃ plans : ClausePlans handler.clauses families, ∃ rows : ClauseRows (clauseSignatures plans),
    ∃ next : Site globals outward world (effect :: residual) actions phases budget ambient
      (installations ++ [endpoint.state.nextHandler]) body runtimeScope
      (.push (.handler handler) endpoint.lexical) result final
      (.handler (effect := effect) (table := table) endpoint.state.nextHandler rows context) root,
    ∃ input : HandlerInput endpoint,
      handler.activation = endpoint.state.nextHandler ∧ handler.scope = runtimeScope ∧
      handler.effectInst = effect ∧ handler.clauses = arms ∧
      HandlerSource globals outward world residual handler result table plans rows
        (actualReceiver world receiving ambient) ∧
      input.data = handler ∧ input.code = body ∧ input.site = nodeId ∧
      input.installation.predecessor = endpoint.state ∧
      input.installation.originalSuffix = endpoint.physical ∧
      input.installation.body = bodyNode ∧
      CoreCallableRichBetaCore.Current (handler_result input).after next ∧
      CoreMachine.next graph endpoint.state = .stepped (handler_result input).after.state ∧
      Matching graph endpoint (handler_result input).after [] [] ∧
      SiteOrigins (handler_result input).after ∧
      EvaluatedScopeOrigins (handler_result input).after ∧
      InstallationsPast program initialInput (handler_result input).after next := by
  obtain ⟨handler,residual,table,families,plans,rows,next,handlerInput,
    activation,scope,effectSame,armsSame,frame,dataSame,codeSame,siteSame,predecessor,
    suffix,bodySame,related,actual,matching,siteOrigins,scopeOrigins⟩ :=
    CoreCallableRichHandlerCore.handler_preserves_from_current_scope ordered run site
      control empty known kind translated siteTranslated closing past.fresh
  have transported := past.operation (.handler handlerInput)
  have appendSame : CoreCallableHandlerPastOrigins.Operation.added_handlers (.handler handlerInput) =
      [endpoint.state.nextHandler] := rfl
  have nextMembership : (installations ++ [endpoint.state.nextHandler]) ⊆
      CoreHandlerHistory.enteredHandlers (handler_result handlerInput).after.state.observations := by
    rw [← appendSame]
    exact transported.2
  exact ⟨handler,residual,table,families,plans,rows,next,handlerInput,
    activation,scope,effectSame,armsSame,frame,dataSame,codeSame,siteSame,predecessor,
    suffix,bodySame,related,actual,matching,siteOrigins,scopeOrigins,⟨transported.1,nextMembership⟩⟩

/-- The negative uses exact current counter membership, not a fabricated
unrelated-state impossibility or equality between private source Families. -/
theorem current_counter_membership_rejected
    (past : InstallationsPast program initialInput endpoint
      (site : Site globals outward world allowed actions phases budget ambient installations
        expression runtimeScope stack result final context root))
    (member : endpoint.state.nextHandler ∈ installations) : False :=
  past.fresh member

end
#print axioms initial_past
#print axioms InstallationsPast.history
#print axioms InstallationsPast.fresh
#print axioms InstallationsPast.operation
#print axioms handler_preserves_with_past
#print axioms current_counter_membership_rejected
end Ash.OneShot.CoreCallableRichHandlerFreshness
