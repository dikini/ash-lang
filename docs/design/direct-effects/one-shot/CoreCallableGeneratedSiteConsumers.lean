import CoreCallableGeneratedSiteOrigins

/-! Actual entry factories consume chronological current-site output. Current
ownership, closure and saved physical-scope obligations remain explicit. -/
namespace Ash.OneShot.CoreCallableGeneratedSiteConsumers
open CoreSyntax CoreTranslation CoreTranslationFuel CoreMachine CoreValueRelation
open CoreStrictStack CoreCallableReachableResume CoreCallableCleanupOrigins
open CoreCallableSiteLineage CoreCallableGeneralHistory CoreCallableRunningOccurrence
open CoreCallableGeneratedChronology ScopedExpressions ScopedExecution

/-- SAME cleanup current data without a caller-supplied current lineage. -/
structure CleanupCurrent (current : Endpoint graph) where
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
  ownership : CurrentOwnership graph current.owners
    {current.state with frames := current.physical} data.scope current.lexical
  control : current.state.control = .evaluate site environment
  empty : EmptyFocus current (.cleanup data.action bodyCode) data.scope

def cleanup_from_generated {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode physical target}
    {current : Endpoint graph} (ordered : Postorder graph)
    (run : Generated start current count created discharged) (input : CleanupCurrent current) :
    CleanupInput current := {
  site := input.site,callback := input.callback,action := input.action,body := input.body,
  environment := input.environment,data := input.data,node := input.node,
  known := input.known,kind := input.kind,shape := input.shape,postorder := ordered,
  lineage := by simpa only [input.empty.focus] using (run.current_site_origins ordered).at input.control,
  rawBody := input.rawBody,bodyCode := input.bodyCode,translated := input.translated,
  closing := input.closing,parameter := input.parameter,lambdaBody := input.lambdaBody,
  callable := input.callable,identity := input.identity,ownership := input.ownership,
  control := input.control,empty := input.empty }

theorem cleanup_actual {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode physical target}
    {current : Endpoint graph} (ordered : Postorder graph)
    (run : Generated start current count created discharged) (input : CleanupCurrent current) :
    CoreMachine.next graph current.state = .stepped (cleanup_result (cleanup_from_generated ordered run input)).after.state ∧
    Matching graph current (cleanup_result (cleanup_from_generated ordered run input)).after [.cleanup input.data.identity] [] :=
  Operation.actual (.cleanup (cleanup_from_generated ordered run input))

theorem cleanup_history_same {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode physical target}
    {current : Endpoint graph} (ordered : Postorder graph)
    (run : Generated start current count created discharged) (input : CleanupCurrent current) :
    (cleanup_data (cleanup_from_generated ordered run input)).past.history = current.history :=
  (cleanup_data (cleanup_from_generated ordered run input)).historySame

/-- The actual handler current input has neither lineage nor a desired
installation/after endpoint; the SAME current history is consumed below. -/
structure HandlerCurrent (current : Endpoint graph) where
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
  origin : CurrentScopeOrigin graph current.owners data.scope current.physical
  activation : data.activation = current.state.nextHandler
  control : current.state.control = .evaluate site environment
  empty : EmptyFocus current (.handle (Instantiation.freezeEffect data.effectInst) code data.clauses) data.scope

structure ProducedHandler {graph : Graph} {current : Endpoint graph} (input : HandlerCurrent current) where
  installation : GeneralHandlerPast graph current.owners input.site input.environment input.data
  predecessor : installation.predecessor = current.state
  suffix : installation.originalSuffix = current.physical
  effect : installation.effect = input.effect
  body : installation.body = input.body

private theorem handler_produced {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode physical target}
    {current : Endpoint graph} (ordered : Postorder graph)
    (run : Generated start current count created discharged) (input : HandlerCurrent current) :
    Nonempty (ProducedHandler input) := by
  have lineage : SiteLineage graph current.owners input.data.scope input.site := by
    simpa only [input.empty.focus] using (run.current_site_origins ordered).at input.control
  obtain ⟨installation,pred,suffix,_,_,_,_,_⟩ := handler_enter_history ordered lineage input.origin current.history
    input.known input.kind input.siteTranslated input.translated input.lexical input.activation
  have sameNode : installation.node = input.node := Option.some.inj (installation.known.symm.trans input.known)
  have sameKind : .handler installation.handler installation.effect installation.body installation.clauses =
      CoreSyntax.Kind.handler input.handler input.effect input.body input.clauses := by
    rw [← installation.kind,sameNode,input.kind]
  obtain ⟨_,effect,body,_⟩ := CoreSyntax.Kind.handler.inj sameKind
  exact ⟨⟨installation,pred,suffix,effect,body⟩⟩

noncomputable def handler_data_from_generated {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode physical target}
    {current : Endpoint graph} (ordered : Postorder graph)
    (run : Generated start current count created discharged) (input : HandlerCurrent current) : ProducedHandler input :=
  Classical.choice (handler_produced ordered run input)

noncomputable def handler_from_generated {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode physical target}
    {current : Endpoint graph} (ordered : Postorder graph)
    (run : Generated start current count created discharged) (input : HandlerCurrent current) : HandlerInput current := {
  owners := current.owners,ownersSame := rfl,site := input.site,environment := input.environment,data := input.data,
  installation := (handler_data_from_generated ordered run input).installation,
  predecessor := (handler_data_from_generated ordered run input).predecessor,
  suffix := (handler_data_from_generated ordered run input).suffix,
  code := input.code,raw := input.raw,rawClauses := input.rawClauses,fuel := input.fuel,
  translated := by rw [(handler_data_from_generated ordered run input).body]; exact input.translated,
  siteTranslated := by rw [(handler_data_from_generated ordered run input).effect]; exact input.siteTranslated,
  lexical := by rw [(handler_data_from_generated ordered run input).effect]; exact input.lexical,
  control := input.control,empty := input.empty }

theorem handler_actual {graph : Graph}
    {start : RunningStartPast graph cleanupOwners action environment data savedValue savedCode physical target}
    {current : Endpoint graph} (ordered : Postorder graph)
    (run : Generated start current count created discharged) (input : HandlerCurrent current) :
    CoreMachine.next graph current.state = .stepped (handler_result (handler_from_generated ordered run input)).after.state ∧
    Matching graph current (handler_result (handler_from_generated ordered run input)).after [] [] :=
  Operation.actual (.handler (handler_from_generated ordered run input))

/-- This saved owner map belongs to the SAME selected handler in current.history;
it is never replaced by the request operand's current owner map. -/
theorem selected_handler_canonical {graph : Graph} (current : Endpoint graph)
    (index : Fin (handler_locations current.history).length) :
    CanonicalOwnerMap graph (location current index).owners :=
  CoreCallableCleanupOrigins.CurrentScopeOrigin.canonical (location current index).installation.origin

#print axioms cleanup_from_generated
#print axioms cleanup_actual
#print axioms cleanup_history_same
#print axioms handler_data_from_generated
#print axioms handler_from_generated
#print axioms handler_actual
#print axioms selected_handler_canonical
end Ash.OneShot.CoreCallableGeneratedSiteConsumers
