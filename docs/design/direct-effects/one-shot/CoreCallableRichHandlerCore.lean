import CoreCallableRichHandlerEntry
import CoreCallableGeneratedCurrentScopeConsumers
import CoreCallableRichBetaCore

namespace Ash.OneShot.CoreCallableRichHandlerCore
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreSyntax CoreMachine CoreTranslation CoreTranslationFuel CoreValueRelation CoreStrictStack
open CoreCallableReachableResume CoreCallableCleanupOrigins CoreCallableGeneralHistory
open CoreCallableRunningOccurrence
open CoreCallableGeneratedChronology CoreCallableGeneratedCurrentScopeConsumers
open CoreCallableContractSource (Contract)
open CoreCallableContractAdmission CoreCallableContractExecution
open SourceDeclarationPlans (ClausePlans)
open SourcePlanSignatures (clauseSignatures)
open SourceDependencyChecks.Lexical (ReturnHints)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (DeclarationPolicy)

section
variable [DeclarationPolicy]

/-- The SAME generated current handler computes its rich body and actual Core
successor. Counter freshness is current evidence, never a chosen replacement. -/
theorem handler_preserves_from_current_scope
    {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action originalEnvironment originalData
      savedValue savedCode physical target}
    {endpoint : Endpoint graph} {hints : ReturnHints receiving} {context : Context hints}
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
    (fresh : endpoint.state.nextHandler ∉ installations) :
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
      EvaluatedScopeOrigins (handler_result input).after := by
  obtain ⟨handler,residual,table,families,plans,rows,next,activation,scope,effectSame,armsSame,frame⟩ :=
    site.enter_handler_at fresh
  let ready : HandlerReady endpoint := {
    site := nodeId,environment := environment,data := handler,node := node,
    handler := binder,effect := rawEffect,body := bodyNode,clauses := rawArms,
    known := known,kind := kind,code := body,raw := rawBody,rawClauses := rawClauses,
    fuel := fuel,translated := translated,siteTranslated := siteTranslated,
    lexical := by simpa only [effectSame,armsSame] using closing,
    activation := activation,control := control,
    empty := by simpa only [effectSame,armsSame,scope] using empty }
  let input := handler_from_current_scope ordered run ready
  have nodeSame : input.installation.node = node :=
    Option.some.inj (input.installation.known.symm.trans known)
  have bodySame : input.installation.body = bodyNode := by
    have same := input.installation.kind.symm.trans (nodeSame ▸ kind)
    exact (CoreSyntax.Kind.handler.inj same).2.2.1
  refine ⟨handler,residual,table,families,plans,rows,next,input,
    activation,scope,effectSame,armsSame,frame,rfl,rfl,rfl,input.predecessor,input.suffix,bodySame,
    ⟨?_⟩,(Operation.actual (.handler input)).1,(Operation.actual (.handler input)).2,
    Operation.site_origins ordered (.handler input) (run.current_site_origins ordered),
    Operation.evaluating_scope (.handler input) run.current_evaluating_scope⟩
  change (handler_result input).after.point.machine = .eval ⟨body,runtimeScope,.push (.handler handler) endpoint.lexical⟩
  simp only [handler_result,Endpoint.point,CoreCleanupRunFrames.attach,Stack.append]
  change LexicalUnwind.Machine.eval ⟨body,handler.scope,.push (.handler handler) endpoint.lexical⟩ = _
  rw [scope]

end

/-- Full prior history is retained as the suffix of the SAME new installation;
no nil-history replacement or projected-store reconstruction is performed. -/
theorem handler_full_history {graph : Graph} {endpoint : Endpoint graph}
    (input : HandlerInput endpoint) :
    (handler_result input).after.history =
      .handler input.installation
        (input.installation.header.heap_weaken (by rw [input.predecessor]; exact fun _ _ h => h))
        endpoint.history := rfl

/-- The actual handler allocation changes only its own counter and observations. -/
theorem handler_runtime_preserved {graph : Graph} {endpoint : Endpoint graph}
    (input : HandlerInput endpoint) :
    (handler_result input).after.owners = endpoint.owners ∧
    (handler_result input).after.state.heap = endpoint.state.heap ∧
    (handler_result input).after.state.nextOwner = endpoint.state.nextOwner ∧
    (handler_result input).after.state.nextActivation = endpoint.state.nextActivation ∧
    (handler_result input).after.state.nextCleanup = endpoint.state.nextCleanup ∧
    (handler_result input).after.state.nextClose = endpoint.state.nextClose ∧
    (handler_result input).after.state.nextHandler = endpoint.state.nextHandler + 1 ∧
    (handler_result input).after.state.observations = endpoint.state.observations ++
      [.entered input.site,.handlerEntered input.site input.data.activation] := by
  exact ⟨input.ownersSame.symm,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms handler_preserves_from_current_scope
#print axioms handler_full_history
#print axioms handler_runtime_preserved
end Ash.OneShot.CoreCallableRichHandlerCore
