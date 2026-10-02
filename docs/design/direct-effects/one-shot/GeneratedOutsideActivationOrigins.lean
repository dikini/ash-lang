import CoreCallableGeneralStartedFrom
namespace Ash.OneShot.GeneratedOutsideActivationOrigins
open CoreSyntax CoreTranslation CoreTranslationFuel CoreMachine CoreValueRelation CoreStrictStack CoreStrictFrames
open ScopedExpressions ScopedExecution CoreCallableGeneratedChronology CoreCallableGeneralHistory
open CoreCallableInitialChronology CoreCallableSiteLineage CoreCallableReachableResume CoreCallableCleanupOrigins
open CoreCallableGeneratedCurrentScopeConsumers CoreCallableGeneratedSiteConsumers CoreCallableCallerBarriers

private noncomputable def handler_current {graph : Graph} {code : Code} {input : InitialInput graph code}
    {current : Endpoint graph} (run : InitialChronology input current count created discharged)
    (ready : HandlerReady current) : HandlerCurrent current := {
  site := ready.site,environment := ready.environment,data := ready.data,node := ready.node
  handler := ready.handler,effect := ready.effect,body := ready.body,clauses := ready.clauses
  known := ready.known,kind := ready.kind,code := ready.code,raw := ready.raw,rawClauses := ready.rawClauses
  fuel := ready.fuel,translated := ready.translated,siteTranslated := ready.siteTranslated,lexical := ready.lexical
  origin := by simpa only [ready.empty.focus] using run.scope_origins.at ready.control
  activation := ready.activation,control := ready.control,empty := ready.empty }

private theorem handler_produced {graph : Graph} {code : Code} {input : InitialInput graph code}
    {current : Endpoint graph} (run : InitialChronology input current count created discharged)
    (ready : HandlerReady current) : Nonempty (ProducedHandler (handler_current run ready)) := by
  let source := handler_current run ready
  have lineage : SiteLineage graph current.owners source.data.scope source.site := by
    simpa only [source.empty.focus] using run.site_origins.at source.control
  obtain ⟨installation,pred,suffix,_,_,_,_,_⟩ := handler_enter_history (checkShape_postorder graph input.shape)
    lineage source.origin current.history source.known source.kind source.siteTranslated source.translated source.lexical source.activation
  have nodeSame := Option.some.inj (installation.known.symm.trans source.known)
  have kinds : CoreSyntax.Kind.handler installation.handler installation.effect installation.body installation.clauses =
      CoreSyntax.Kind.handler source.handler source.effect source.body source.clauses := by
    rw [← installation.kind,nodeSame,source.kind]
  obtain ⟨_,effect,body,_⟩ := CoreSyntax.Kind.handler.inj kinds
  exact ⟨⟨installation,pred,suffix,effect,body⟩⟩

noncomputable def handler_data_from_initial {graph : Graph} {code : Code} {input : InitialInput graph code}
    {current : Endpoint graph} (run : InitialChronology input current count created discharged)
    (ready : HandlerReady current) : ProducedHandler (handler_current run ready) :=
  Classical.choice (handler_produced run ready)

noncomputable def handler_from_initial {graph : Graph} {code : Code} {input : InitialInput graph code}
    {current : Endpoint graph} (run : InitialChronology input current count created discharged)
    (ready : HandlerReady current) : HandlerInput current := {
  owners := current.owners,ownersSame := rfl,site := ready.site,environment := ready.environment,data := ready.data
  installation := (handler_data_from_initial run ready).installation
  predecessor := (handler_data_from_initial run ready).predecessor
  suffix := (handler_data_from_initial run ready).suffix
  code := ready.code,raw := ready.raw,rawClauses := ready.rawClauses,fuel := ready.fuel
  translated := by simpa only [(handler_data_from_initial run ready).body,handler_current] using ready.translated
  siteTranslated := by simpa only [(handler_data_from_initial run ready).effect,handler_current] using ready.siteTranslated
  lexical := by simpa only [(handler_data_from_initial run ready).effect,handler_current] using ready.lexical
  control := ready.control,empty := ready.empty }

theorem handler_literal_fields {graph : Graph} {code : Code} {input : InitialInput graph code}
    {current : Endpoint graph} (run : InitialChronology input current count created discharged)
    (ready : HandlerReady current) :
    (handler_from_initial run ready).installation.handler = ready.handler ∧
    (handler_from_initial run ready).installation.body = ready.body ∧
    (handler_from_initial run ready).installation.effect = ready.effect ∧
    (handler_from_initial run ready).installation.clauses = ready.clauses := by
  let past := (handler_from_initial run ready).installation
  have nodeSame := Option.some.inj (past.known.symm.trans ready.known)
  have kinds : CoreSyntax.Kind.handler past.handler past.effect past.body past.clauses =
      CoreSyntax.Kind.handler ready.handler ready.effect ready.body ready.clauses := by
    rw [← past.kind,nodeSame,ready.kind]
  obtain ⟨handler,effect,body,clauses⟩ := CoreSyntax.Kind.handler.inj kinds
  exact ⟨handler,body,effect,clauses⟩

theorem handler_current_control {graph : Graph} {code : Code} {input : InitialInput graph code}
    {current : Endpoint graph} (run : InitialChronology input current count created discharged)
    (ready : HandlerReady current) :
    (handler_result (handler_from_initial run ready)).after.state.control = .evaluate ready.body ready.environment := by
  change CoreMachine.Control.evaluate (handler_from_initial run ready).installation.body ready.environment = _
  rw [(handler_literal_fields run ready).2.1]

/-- The original cleanup scope comes from the immediately preceding actual
handler endpoint. There is no caller-provided saved-scope equality. -/
theorem cleanup_saved_scope {graph : Graph} {before : Endpoint graph} (handler : HandlerInput before)
    (ready : CleanupReady (handler_result handler).after) : ready.data.scope = handler.data.scope := by
  have scopes := congrArg Configuration.scope ready.empty.focus
  simpa only [handler_result] using scopes.symm

theorem handler_owner_map {graph : Graph} {before : Endpoint graph} (handler : HandlerInput before) :
    (handler_result handler).after.owners = before.owners := handler.ownersSame.symm

/-- Named callback operations with unchanged heap/history. The explicit family
has no caller-provided history equality or successor. -/
inductive StableOperation : (before after : Endpoint graph) → Type where
  | entry (input : EntryInput before) : StableOperation before (entry_result input).after
  | literal (input : LiteralInput before) : StableOperation before (literal_result input).after
  | swap (input : SwapInput before) : StableOperation before (swap_result input).after
  | beta (input : BetaInput before) : StableOperation before (beta_result input).after
noncomputable def StableOperation.operation {graph : Graph} {before after : Endpoint graph}
    (stable : StableOperation before after) : Operation before after [] [] :=
  match stable with
  | .entry input => .entry input
  | .literal input => .literal input
  | .swap input => .swap input
  | .beta input => .beta input

theorem StableOperation.same_heap {graph : Graph} {before after : Endpoint graph}
    (stable : StableOperation before after) : after.state.heap = before.state.heap := by
  cases stable <;> rfl

theorem StableOperation.same_history {graph : Graph} {before after : Endpoint graph}
    (stable : StableOperation before after) : HEq after.history before.history := by
  cases stable <;> rfl

inductive StableSegment (first : Endpoint graph) : Endpoint graph → Nat → Type where
  | initial : StableSegment first first 0
  | next (earlier : StableSegment first before count) (step : StableOperation before after) :
      StableSegment first after (count+1)

theorem StableSegment.same_history {graph : Graph} {first after : Endpoint graph}
    (stable : StableSegment first after count) : HEq after.history first.history := by
  induction stable with
  | initial => rfl
  | next earlier step ih => exact step.same_history.trans ih

noncomputable def StableSegment.generated {graph : Graph}
    {start : CoreCallableRunningOccurrence.RunningStartPast graph owners action environment data savedValue savedCode physical target}
    {after : Endpoint graph} (stable : StableSegment (started start) after count) : Generated start after count [] [] := by
  induction stable with
  | initial => exact .initial
  | next earlier step ih => simpa using Generated.next ih step.operation

#print axioms handler_from_initial
#print axioms handler_literal_fields
#print axioms handler_current_control
#print axioms cleanup_saved_scope
#print axioms handler_owner_map
#print axioms StableOperation.same_history
#print axioms StableSegment.same_history
#print axioms StableSegment.generated
end Ash.OneShot.GeneratedOutsideActivationOrigins
