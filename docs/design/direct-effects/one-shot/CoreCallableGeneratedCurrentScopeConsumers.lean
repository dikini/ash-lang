import CoreCallableGeneratedCurrentScopeOrigins
import CoreCallableGeneratedTicketBound
namespace Ash.OneShot.CoreCallableGeneratedCurrentScopeConsumers
open CoreSyntax CoreTranslation CoreTranslationFuel CoreMachine CoreValueRelation
open CoreStrictStack CoreCallableReachableResume CoreCallableCleanupOrigins
open CoreCallableSiteLineage CoreCallableGeneralHistory CoreCallableRunningOccurrence
open CoreCallableGeneratedChronology CoreCallableGeneratedTicketBound
open CoreCallableGeneratedSiteConsumers ScopedExpressions ScopedExecution

/-- Actual control inversion exposes dynamic occurrence. Only the existing
original-start ticket bound is consumed; no current bound enters this interface. -/
theorem ownership_at_evaluate {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action originalEnvironment data savedValue savedCode physical target}
    {current : Endpoint graph} (run : Generated start current count created discharged)
    (initial : TicketBound (start_before start).state target)
    (control : current.state.control = .evaluate site currentEnvironment)
    (scopeSame : current.focus.scope = scope) :
    CurrentOwnership graph current.owners {current.state with frames := current.physical} scope current.lexical := by
  refine ⟨?_,?_⟩
  · simpa only [TicketBound] using Generated.lexical_ticket_bound run initial
  · simpa only [scopeSame] using run.current_evaluating_scope.at control

/-- SAME cleanup current data without either lineage or current ownership. -/
structure CleanupReady (current : Endpoint graph) where
  site : Nat
  callback : Binder
  action : Nat
  body : Nat
  environment : Environment
  data : ActionData
  node : CoreSyntax.Node
  known : graph.node site = some node
  kind : node.kind = .cleanup callback action body
  shape : checkCleanup graph site callback action = .ok ()
  rawBody : Code
  bodyCode : Code
  translated : translateFuel graph (graph.nodes.length+1) current.owners body = .ok rawBody
  closing : EnvCloses graph current.owners current.state.heap environment
    (.cleanup (.variable callback.id) rawBody) (.cleanup data.action bodyCode)
  parameter : Nat
  lambdaBody : Code
  callable : data.action = .lambda parameter lambdaBody
  identity : data.identity = current.state.nextCleanup
  control : current.state.control = .evaluate site environment
  empty : EmptyFocus current (.cleanup data.action bodyCode) data.scope

def cleanup_from_current_scope {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode physical target}
    {current : Endpoint graph} (ordered : Postorder graph)
    (run : Generated start current count created discharged)
    (initial : TicketBound (start_before start).state target) (input : CleanupReady current) : CleanupInput current :=
  cleanup_from_generated ordered run {
    site := input.site,callback := input.callback,action := input.action,body := input.body,
    environment := input.environment,data := input.data,node := input.node,known := input.known,
    kind := input.kind,shape := input.shape,rawBody := input.rawBody,bodyCode := input.bodyCode,
    translated := input.translated,closing := input.closing,parameter := input.parameter,
    lambdaBody := input.lambdaBody,callable := input.callable,identity := input.identity,
    ownership := ownership_at_evaluate run initial input.control (by rw [input.empty.focus]),
    control := input.control,empty := input.empty }

theorem cleanup_actual {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode physical target}
    {current : Endpoint graph} (ordered : Postorder graph)
    (run : Generated start current count created discharged)
    (initial : TicketBound (start_before start).state target) (input : CleanupReady current) :
    CoreMachine.next graph current.state = .stepped (cleanup_result (cleanup_from_current_scope ordered run initial input)).after.state ∧
    Matching graph current (cleanup_result (cleanup_from_current_scope ordered run initial input)).after [.cleanup input.data.identity] [] :=
  Operation.actual (.cleanup (cleanup_from_current_scope ordered run initial input))

theorem cleanup_history_same {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode physical target}
    {current : Endpoint graph} (ordered : Postorder graph)
    (run : Generated start current count created discharged)
    (initial : TicketBound (start_before start).state target) (input : CleanupReady current) :
    (cleanup_data (cleanup_from_current_scope ordered run initial input)).past.history = current.history :=
  (cleanup_data (cleanup_from_current_scope ordered run initial input)).historySame

/-- SAME handler current data without lineage, current origin or installation. -/
structure HandlerReady (current : Endpoint graph) where
  site : Nat
  environment : Environment
  data : HandlerData
  node : CoreSyntax.Node
  handler : Nat
  effect : Instantiation.Effect
  body : Nat
  clauses : List CoreSyntax.Clause
  known : graph.node site = some node
  kind : node.kind = .handler handler effect body clauses
  code : Code
  raw : Code
  rawClauses : Clauses
  fuel : Nat
  translated : translateFuel graph fuel current.owners body = .ok raw
  siteTranslated : translateFuel graph (fuel+1) current.owners site = .ok (.handle effect raw rawClauses)
  lexical : EnvCloses graph current.owners current.state.heap environment
    (.handle effect raw rawClauses) (.handle (Instantiation.freezeEffect data.effectInst) code data.clauses)
  activation : data.activation = current.state.nextHandler
  control : current.state.control = .evaluate site environment
  empty : EmptyFocus current (.handle (Instantiation.freezeEffect data.effectInst) code data.clauses) data.scope

noncomputable def handler_from_current_scope {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode physical target}
    {current : Endpoint graph} (ordered : Postorder graph)
    (run : Generated start current count created discharged) (input : HandlerReady current) : HandlerInput current :=
  handler_from_generated ordered run {
    site := input.site,environment := input.environment,data := input.data,node := input.node,
    handler := input.handler,effect := input.effect,body := input.body,clauses := input.clauses,
    known := input.known,kind := input.kind,code := input.code,raw := input.raw,
    rawClauses := input.rawClauses,fuel := input.fuel,translated := input.translated,
    siteTranslated := input.siteTranslated,lexical := input.lexical,
    origin := by simpa only [input.empty.focus] using run.current_evaluating_scope.at input.control,
    activation := input.activation,control := input.control,empty := input.empty }

theorem handler_actual {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode physical target}
    {current : Endpoint graph} (ordered : Postorder graph)
    (run : Generated start current count created discharged) (input : HandlerReady current) :
    CoreMachine.next graph current.state = .stepped (handler_result (handler_from_current_scope ordered run input)).after.state ∧
    Matching graph current (handler_result (handler_from_current_scope ordered run input)).after [] [] :=
  Operation.actual (.handler (handler_from_current_scope ordered run input))

#print axioms ownership_at_evaluate
#print axioms cleanup_from_current_scope
#print axioms cleanup_actual
#print axioms cleanup_history_same
#print axioms handler_from_current_scope
#print axioms handler_actual
end Ash.OneShot.CoreCallableGeneratedCurrentScopeConsumers
