import CoreCallableRichAdmittedCurrentOrigins
import CoreCallableGeneralStartedFrom
import CoreCallableGeneratedCleanupCompletion
import CoreCallableRichBranchCurrentOrigins

/-! UNCOMPILED complete decomposition subset for a bounded normal-cleanup phase
experiment. These lemmas retain exact rich callback/body contracts and rows and
project current contextual checks/accounting. Runtime edges are reused separately.
They do not construct full rich registration/entry/finish successor authority. -/
namespace Ash.OneShot.CoreCallableRichNormalCleanupPhases
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreSyntax CoreMachine CoreCallableGeneratedChronology
open CoreCallableInitialChronology CoreCallableGeneralHistory CoreCallableRunningOccurrence
open CoreCallableGeneratedCleanupCompletion CoreCallableReachableResume
open CoreCallableContractAdmission CoreCallableContractExecution
open CoreCallableContractSource (Contract Environment)
open SourceDeclarationPlans (Plan)
open SourceDependencyAnnotations (Dependencies)
open SourcePlanSignatures (signature)
open SourceDependencyChecks.Lexical (ReturnHints)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (Certified DeclarationPolicy)

variable {graph : Graph} {endpoint : Endpoint graph}

section
variable [evidence : DeclarationPolicy]

/-- One nonrecursive view of the original rich cleanup constructor. The index
retains its SAME source proof and all callback/body private plans and rows. -/
inductive CleanupSourceParts
    (registry : CoreCallableContractRegistries.Registry) (outward : List Instance)
    (owners : CoreCallableContractRegistries.Owners) (world : List Nat)
    (allowed : List Instance) (scope : Execution.Scope) (environment : CoreCallableContractSource.Environment)
    (action body : Code) (output : Contract) :
    {demand : List Nat} → {requirements : RecursiveRequirements.Requirements demand} →
    {dependencies : Dependencies} → {plan : Plan dependencies} → {rows : Rows (signature plan)} →
    IndexedSource registry outward owners world allowed scope environment
      (.cleanup action body) output demand requirements plan rows → Prop where
  | cleanup
      {callbackDependencies : Dependencies} {callbackPlan : Plan callbackDependencies}
      {callbackRows : Rows (signature callbackPlan)}
      (callback : IndexedSource registry outward owners world allowed scope environment action
        (Contract.function .unit .unit requests latent callbackPlan callbackRows)
        callbackDemand callbackRequirements actualCallbackPlan actualCallbackRows)
      (bodySource : IndexedSource registry outward owners world allowed scope environment body
        output bodyDemand bodyRequirements bodyPlan bodyRows)
      (admitted : requests ⊆ allowed) (certified : Certified outward world callbackPlan) :
      CleanupSourceParts registry outward owners world allowed scope environment action body output
        (IndexedSource.cleanup callback bodySource admitted certified)

/-- Inversion exposes only evidence already held by the current source. -/
theorem cleanup_source_parts
    (source : IndexedSource registry outward owners world allowed scope environment
      (.cleanup action body) output demand requirements plan rows) :
    CleanupSourceParts registry outward owners world allowed scope environment action body output source := by
  cases source with
  | cleanup callback bodySource admitted certified =>
      exact .cleanup callback bodySource admitted certified

/-- A current authentication receipt retains the actual constructor-selected
callback/body sources and their private metadata together. It does not select
independent child derivations from an aggregate demand append equality. -/
inductive CleanupAuthenticationParts
    (registry : CoreCallableContractRegistries.Registry) (outward : List Instance)
    (owners : CoreCallableContractRegistries.Owners) (world : List Nat)
    (allowed : List Instance) (scope : Execution.Scope)
    (environment : CoreCallableContractSource.Environment)
    (action body : Code) (output : Contract)
    (lexical : CoreCallableReceiverRefinement.LexicalBounds) (receiver : List Nat) :
    {demand : List Nat} → {requirements : RecursiveRequirements.Requirements demand} →
    {dependencies : Dependencies} → {plan : Plan dependencies} →
    {rows : Rows (signature plan)} →
    (source : IndexedSource registry outward owners world allowed scope environment
      (.cleanup action body) output demand requirements plan rows) →
    Authenticated registry outward source lexical receiver → Prop where
  | cleanup
      {callbackDependencies : Dependencies} {callbackPlan : Plan callbackDependencies}
      {callbackRows : Rows (signature callbackPlan)}
      (callback : IndexedSource registry outward owners world allowed scope environment action
        (Contract.function .unit .unit requests latent callbackPlan callbackRows)
        callbackDemand callbackRequirements actualCallbackPlan actualCallbackRows)
      (bodySource : IndexedSource registry outward owners world allowed scope environment body
        output bodyDemand bodyRequirements bodyPlan bodyRows)
      (admitted : requests ⊆ allowed) (certified : Certified outward world callbackPlan)
      (currentSupport :
        SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Bounds lexical.environment
        (Code.cleanup action body).dependencies receiver)
      (callbackAuthentication : Authenticated registry outward callback lexical receiver)
      (bodyAuthentication : Authenticated registry outward bodySource lexical receiver) :
      CleanupAuthenticationParts registry outward owners world allowed scope environment
        action body output lexical receiver (IndexedSource.cleanup callback bodySource admitted certified)
        (.checked currentSupport
          (.cleanup (admitted := admitted) (publicCertified := certified)
            callbackAuthentication bodyAuthentication))

/-- Inversion retains the SAME current Source/Auth receipt and the actual full
child annotations selected by its recursive authentication constructor. -/
theorem cleanup_authentication_parts
    (source : IndexedSource registry outward owners world allowed scope environment
      (.cleanup action body) output demand requirements plan rows)
    (authenticated : Authenticated registry outward source lexical receiver) :
    CleanupAuthenticationParts registry outward owners world allowed scope environment
      action body output lexical receiver source authenticated := by
  cases authenticated with
  | checked currentSupport hereditary =>
      cases hereditary with
      | cleanup callbackAuthentication bodyAuthentication =>
          rename_i certified admitted callbackSource bodySource
          exact .cleanup callbackSource bodySource admitted certified currentSupport
            callbackAuthentication bodyAuthentication

end

/-- Installation checking projects the actual body and normal callback contexts. -/
theorem cleanup_code_parts
    (checked : SourceAdmission.Code outward actions budget phases world installations
      (Rows.cleanup (needs := needs) latent callbackRows bodyRows) context) :
    SourceAdmission.Code outward actions budget phases world installations bodyRows
      (Context.cleanup (needs := needs) latent callbackRows context) ∧
    SourceAdmission.Code outward actions budget phases world installations callbackRows
      (Context.normal context) := by
  cases checked with
  | cleanup body callback => exact ⟨body, callback⟩

/-- Resource checking accompanies those SAME certificate proofs. -/
theorem cleanup_resource_parts
    {body : SourceAdmission.Code outward actions budget phases world installations bodyRows
      (Context.cleanup (needs := needs) latent callbackRows context)}
    {callback : SourceAdmission.Code outward actions budget phases world installations callbackRows
      (Context.normal context)}
    (checked : InstallationSupport.CodeChecked ambient outward
      (SourceAdmission.Code.cleanup body callback)) :
    InstallationSupport.CodeChecked ambient outward body ∧
      InstallationSupport.CodeChecked ambient outward callback := by
  cases checked with
  | cleanup inside closing => exact ⟨inside, closing⟩

/-- The body inherits the exact executable root, without a new root premise. -/
theorem cleanup_run_body
    (accounting : Accounting.Run world installations
      (Rows.cleanup (needs := needs) latent callbackRows bodyRows) context root) :
    Accounting.Run world installations bodyRows
      (Context.cleanup (needs := needs) latent callbackRows context) root := by
  cases accounting with
  | installCleanup body => exact body

/-- A completed ordinary body selects the callback at the original root. -/
theorem cleanup_wait_callback
    (waiting : Accounting.Wait world installations
      (Context.cleanup (needs := needs) latent callbackRows context) .ordinary root) :
    Accounting.Run world installations callbackRows (context.callback .ordinary) root := by
  cases waiting with
  | cleanup callback => exact callback

/-- Registration is the existing actual typed edge, with no new ticket capture.
This runtime projection is not a rich successor Site. -/
theorem registration_runtime (input : CleanupInput endpoint) :
    CoreMachine.next graph endpoint.state = .stepped (cleanup_result input).after.state ∧
    RawStep ⟨.cleanup input.data.action input.bodyCode, input.data.scope, endpoint.lexical⟩
      ⟨input.bodyCode, input.data.scope, .push (.armed input.data) endpoint.lexical⟩
      [.cleanup input.data.identity] [] ∧
    CoreTicketHistory.capturedTickets (cleanup_result input).after.state.observations =
      CoreTicketHistory.capturedTickets endpoint.state.observations := by
  refine ⟨(cleanup_result input).core, (cleanup_data input).raw, ?_⟩
  simpa only [issuedTickets, List.filterMap_cons, List.filterMap_nil, List.append_nil] using
    CoreCallableGeneratedTicketBound.Operation.ticket_events (.cleanup input)

/-- Finish retains the actual same-start restoration and ownership projection.
A full rich saved-result Site must still be constructed by the phase bridge. -/
theorem finish_runtime
    {start : RunningStartPast graph cleanupOwners action environment data
      savedValue savedCode physical target}
    {endpoint : Endpoint graph}
    {generated : Generated start endpoint count created discharged}
    (input : FinishInput generated)
    (initialBound : TicketBound (start_before start).state target) :
    CoreMachine.next graph endpoint.state = .stepped (finish_result input).after.state ∧
    CurrentOwnership graph cleanupOwners (finish_result input).after.state
      data.scope input.head.tail.target :=
  ⟨(finish_result input).core, CoreCallableGeneratedTicketBound.finish_current_ownership_generated input initialBound⟩

section
variable [evidence : DeclarationPolicy]

/-- A returned rich value keeps its full result Contract and private captures.
Only immediate checking rows are summarized; the executable root is unchanged. -/
theorem normal_saved_value
    (source : Source globals outward world allowed scope environment value contract
      sourceDemand sourceRequirements plan rows)
    (authenticated : Authenticated globals.registry outward source lexical receiver)
    (closed : ClosedValue value)
    (accounting : Accounting.Run world installations rows context root) :
    Authenticated globals.registry outward (IndexedSource.value_summary source closed.1) lexical receiver ∧
      Accounting.Wait world installations context .ordinary root := by
  exact ⟨authenticated.value_summary closed.1,
    (Accounting.silent_iff (Source.value_silent source closed.1) rows).mp accounting⟩

/-- Literal registration removes only the already evaluated callback prefix.
The body and callback retain their own exact contextual certificates and root. -/
theorem normal_registration_checks
    (callback : Source globals outward world allowed scope Environment.empty action callbackContract
      callbackDemand callbackRequirements actualCallbackPlan actualCallbackRows)
    (closed : ClosedValue action)
    (certificate : SourceAdmission.Code outward actions budget phases world installations
      (Rows.sequence actualCallbackRows
        (Rows.cleanup (needs := needs) latent callbackRows bodyRows)) context)
    (checked : InstallationSupport.CodeChecked ambient outward certificate)
    (accounting : Accounting.Run world installations
      (Rows.sequence actualCallbackRows
        (Rows.cleanup (needs := needs) latent callbackRows bodyRows)) context root) :
    ∃ bodyCertificate : SourceAdmission.Code outward actions budget phases world installations bodyRows
      (Context.cleanup (needs := needs) latent callbackRows context),
    ∃ callbackCertificate : SourceAdmission.Code outward actions budget phases world installations callbackRows
      (Context.normal context),
      InstallationSupport.CodeChecked ambient outward bodyCertificate ∧
      InstallationSupport.CodeChecked ambient outward callbackCertificate ∧
      Accounting.Run world installations bodyRows
        (Context.cleanup (needs := needs) latent callbackRows context) root := by
  have afterPrefix :=
    (Accounting.silent_prefix_iff (Source.value_silent callback closed.1)
      actualCallbackRows (Rows.cleanup (needs := needs) latent callbackRows bodyRows)).mp accounting
  cases certificate with
  | sequence first cleanup =>
      cases checked with
      | sequence firstChecked cleanupChecked =>
          cases cleanup with
          | cleanup bodyCertificate callbackCertificate =>
              cases cleanupChecked with
              | cleanup bodyChecked callbackChecked =>
                  exact ⟨bodyCertificate, callbackCertificate, bodyChecked, callbackChecked,
                    cleanup_run_body afterPrefix⟩

/-- The completed normal callback releases its boundary at the SAME original
root. A separate retained rich saved value supplies the restored expression. -/
theorem normal_callback_finished_wait
    (source : Source globals outward world allowed scope Environment.empty value .unit
      sourceDemand sourceRequirements plan rows)
    (closed : ClosedValue value)
    (accounting : Accounting.Run world installations rows (Context.normal context) root) :
    Accounting.Wait world installations context .ordinary root := by
  have waiting := (Accounting.silent_iff (Source.value_silent source closed.1) rows).mp accounting
  cases waiting with
  | normal tail => exact tail

/-- Current callback source and its existing normal-context checks construct
ordinary Unit application authority at inactive scope with the identical root.
This is a local contextual composition, not a full runtime phase bridge. -/
theorem normal_callback_application
    {callbackDependencies : Dependencies} {callbackPlan : Plan callbackDependencies}
    {callbackRows : Rows (signature callbackPlan)}
    (callback : IndexedSource registry outward owners world allowed scope Environment.empty action
      (Contract.function .unit .unit requests latent callbackPlan callbackRows)
      callbackDemand callbackRequirements actualCallbackPlan actualCallbackRows)
    (authenticated : Authenticated registry outward callback lexical receiver)
    (closed : ClosedValue action)
    (certified : Certified outward world callbackPlan)
    (callbackCertificate : SourceAdmission.Code outward actions budget phases world installations
      callbackRows (Context.normal context))
    (callbackChecked : InstallationSupport.CodeChecked ambient outward callbackCertificate)
    (callbackRun : Accounting.Run world installations callbackRows (Context.normal context) root) :
    let applicationPlan : Plan _ := .sequence .pure (.sequence .pure callbackPlan)
    let applicationRows : Rows (signature applicationPlan) :=
      CoreCallableContractSource.sequenceRows Rows.pure
        (CoreCallableContractSource.sequenceRows Rows.pure callbackRows)
    ∃ applicationSource : IndexedSource registry outward owners world requests .none Environment.empty
      (.app action .unit) .unit []
      (.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent)
      applicationPlan applicationRows,
      Authenticated registry outward applicationSource lexical receiver ∧
      ∃ applicationCertificate : SourceAdmission.Code outward actions budget phases world installations
        applicationRows (Context.normal context),
        InstallationSupport.CodeChecked ambient outward applicationCertificate ∧
        Accounting.Run world installations applicationRows (Context.normal context) root := by
  let summary := IndexedSource.value_summary callback closed.1
  let inactive := IndexedSource.value_allowed summary closed.1 requests .none
  have inactiveAuth : Authenticated registry outward inactive lexical receiver :=
    (authenticated.value_summary closed.1).value_allowed closed.1 requests .none
  let unitSource : IndexedSource registry outward owners world requests .none Environment.empty
      .unit .unit [] (.request [] []) .pure Rows.pure := .unit
  let applicationSource := IndexedSource.app inactive unitSource (List.Subset.refl requests) certified
  have applicationAuth : Authenticated registry outward applicationSource lexical receiver := by
    apply Authenticated.checked
    · simpa only [Code.dependencies, List.append_nil] using inactiveAuth.current_support
    · exact .app (admitted := List.Subset.refl requests) (publicCertified := certified)
        inactiveAuth (.checked .nil .unit)
  let applicationCertificate := SourceAdmission.Code.sequence
    (SourceAdmission.Code.pure) (SourceAdmission.Code.sequence .pure callbackCertificate)
  have applicationChecked : InstallationSupport.CodeChecked ambient outward applicationCertificate :=
    .sequence .pure (.sequence .pure callbackChecked)
  have applicationRun : Accounting.Run world installations
      (Rows.sequence Rows.pure (Rows.sequence Rows.pure callbackRows))
      (Context.normal context) root :=
    .sequence (.pure (.plain (.sequence (.pure (.plain callbackRun)))))
  exact ⟨applicationSource, applicationAuth, applicationCertificate,
    applicationChecked, applicationRun⟩

end


section
variable [evidence : DeclarationPolicy]

/-- Rich cleanup annotations are proof-side metadata. Identity, action, scope,
code, closure/environment guards and actual Core registration inputs are kept.
The canonical answer is produced from the current FULL result Contract. -/
def CleanupInput.with_annotation (input : CleanupInput endpoint) (answer : Ty)
    (requests : List Instance) : CleanupInput endpoint :=
  { input with data := { input.data with answer := answer, requests := requests } }

omit evidence in
/-- This is equality of the complete actual computed Core state, not an assumed
future endpoint equality. Target cleanup annotations deliberately differ. -/
theorem cleanup_annotation_state (input : CleanupInput endpoint) (answer : Ty)
    (requests : List Instance) :
    (cleanup_result (CleanupInput.with_annotation input answer requests)).after.state =
      (cleanup_result input).after.state := rfl

omit evidence in
/-- Canonical proof-side annotation keeps the original successful Core edge. -/
theorem cleanup_annotation_actual (input : CleanupInput endpoint) (answer : Ty)
    (requests : List Instance) :
    CoreMachine.next graph endpoint.state =
      .stepped (cleanup_result (CleanupInput.with_annotation input answer requests)).after.state :=
  (cleanup_result (CleanupInput.with_annotation input answer requests)).core

omit evidence in
/-- The start/finish Core state builders use the same retained runtime value,
identity and physical suffix; neither reads answer/requests proof metadata. -/
theorem normal_start_annotation_state (input : CleanupInput endpoint) (answer : Ty)
    (requests : List Instance) (base : CoreMachine.State) (savedValue : CoreMachine.Value)
    (physical : List CoreMachine.Frame) :
    CoreGeneralRestoration.startedState base input.action input.environment
      (CleanupInput.with_annotation input answer requests).data.identity savedValue physical =
    CoreGeneralRestoration.startedState base input.action input.environment
      input.data.identity savedValue physical := rfl

omit evidence in
theorem normal_finish_annotation_state (input : CleanupInput endpoint) (answer : Ty)
    (requests : List Instance) (base : CoreMachine.State) (savedValue : CoreMachine.Value)
    (physical : List CoreMachine.Frame) :
    CoreGeneralRestoration.observedState base savedValue physical
      (.cleanupFinished (CleanupInput.with_annotation input answer requests).data.identity) =
    CoreGeneralRestoration.observedState base savedValue physical
      (.cleanupFinished input.data.identity) := rfl

/-- This facet indexes the entire SAME current Site. The saved value keeps the
full Contract, including latent private function families, rather than answerTy.
Only its immediate value rows are summarized; the original executable root and
whole retained Pending remain available from the indexed Site. -/
structure FullSavedValueAuthority {receiving : SourceDependencyCapture.Scope}
    {hints : ReturnHints receiving} {context : Context hints}
    (site : Site globals outward world allowed actions phases budget ambient installations
      value runtimeScope stack result final context root)
    (related : CoreValueRelation.ValueRel graph endpoint.owners endpoint.state.heap runtimeValue value) : Prop where
  source : Source globals outward world allowed runtimeScope Environment.empty value result
    [] (.request [] []) .pure Rows.pure
  original : source = IndexedSource.value_summary site.current.source related.closed.1
  authentication : ∃ lexical : CoreCallableReceiverRefinement.LexicalBounds,
    lexical.environment = ScopedPorts.Support.empty ∧
    Authenticated globals.registry outward source lexical (actualReceiver world receiving ambient)
  certificate : SourceAdmission.Code outward actions budget phases world installations Rows.pure context
  certificateChecked : InstallationSupport.CodeChecked ambient outward certificate
  waiting : Accounting.Wait world installations context .ordinary root

/-- The actual current runtime value supplies closedness, while the SAME current
rich Source supplies the complete result annotation. ValueRel alone is not used
to reconstruct any latent contract or source derivation. -/
theorem full_saved_value_authority {receiving : SourceDependencyCapture.Scope}
    {hints : ReturnHints receiving} {context : Context hints}
    (site : Site globals outward world allowed actions phases budget ambient installations
      value runtimeScope stack result final context root)
    (related : CoreValueRelation.ValueRel graph endpoint.owners endpoint.state.heap runtimeValue value) :
    FullSavedValueAuthority site related := by
  let summary := IndexedSource.value_summary site.current.source related.closed.1
  obtain ⟨lexical, sameEnvironment, authenticated⟩ := site.current.authentication
  exact ⟨summary, rfl, ⟨lexical, sameEnvironment, authenticated.value_summary related.closed.1⟩,
    .pure, .pure,
    (Accounting.silent_iff (Source.value_silent site.current.source related.closed.1) site.rows).mp site.accounting⟩

/-- Old pending evidence is retained unchanged, at the exact full saved Contract.
This is available from the whole current Site, not inferred from an erased Ty. -/
theorem FullSavedValueAuthority.pending {receiving : SourceDependencyCapture.Scope}
    {hints : ReturnHints receiving} {context : Context hints}
    {site : Site globals outward world allowed actions phases budget ambient installations
      value runtimeScope stack result final context root}
    {related : CoreValueRelation.ValueRel graph endpoint.owners endpoint.state.heap runtimeValue value}
    (saved : FullSavedValueAuthority site related) :
    Pending globals outward world allowed ambient stack result final context := by
  cases saved
  exact site.pending

/-- One bounded additive pending interface, with the entire accepted Pending as
its base. Armed/running cases store full current callback and saved-value source
contracts. They do not alter Core or repeat the old pending constructor grammar.
The runtime answer annotation is a current synchronization obligation; a rich
registration producer must derive it before using either phase constructor. -/
inductive PhasePending (globals : Globals) (outward : List Instance) (world : List Nat) :
    List Instance → List Nat → Stack → Contract → Contract →
    {scope : SourceDependencyCapture.Scope} → {hints : ReturnHints scope} → Context hints → Prop where
  | original (pending : Pending globals outward world allowed ambient stack input output context) :
      PhasePending globals outward world allowed ambient stack input output context
  | armed {data : ActionData} {receiving : SourceDependencyCapture.Scope}
      {hints : ReturnHints receiving} {context : Context hints}
      {callbackDependencies : Dependencies} {callbackPlan : Plan callbackDependencies}
      {callbackRows : Rows (signature callbackPlan)}
      (callback : Source globals outward world allowed data.scope Environment.empty data.action
        (Contract.function .unit .unit requests latent callbackPlan callbackRows)
        callbackDemand callbackRequirements actualCallbackPlan actualCallbackRows)
      (authenticated : ∃ lexical : CoreCallableReceiverRefinement.LexicalBounds,
        Authenticated globals.registry outward callback lexical (actualReceiver world receiving ambient))
      (certified : Certified outward world callbackPlan)
      (requestsSame : data.requests = requests)
      (answerSame : ScopedPorts.eraseType data.answer = input.port)
      (tail : Pending globals outward world allowed ambient stack input output context) :
      PhasePending globals outward world allowed ambient (.push (.armed data) stack) input output
        (Context.cleanup (needs := requests) latent callbackRows context)
  | running {data : ActionData} {receiving : SourceDependencyCapture.Scope}
      {hints : ReturnHints receiving} {context : Context hints}
      {callbackDependencies : Dependencies} {callbackPlan : Plan callbackDependencies}
      {callbackRows : Rows (signature callbackPlan)}
      (callback : Source globals outward world callbackSourceAllowed data.scope Environment.empty data.action
        (Contract.function .unit .unit requests latent callbackPlan callbackRows)
        callbackDemand callbackRequirements actualCallbackPlan actualCallbackRows)
      (callbackAuthentication : ∃ lexical : CoreCallableReceiverRefinement.LexicalBounds,
        Authenticated globals.registry outward callback lexical (actualReceiver world receiving ambient))
      (certified : Certified outward world callbackPlan)
      (requestsSame : data.requests = requests)
      (closed : ClosedValue savedCode)
      (saved : Source globals outward world savedAllowed data.scope Environment.empty savedCode input
        [] (.request [] []) .pure Rows.pure)
      (authenticated : ∃ lexical : CoreCallableReceiverRefinement.LexicalBounds,
        Authenticated globals.registry outward saved lexical (actualReceiver world receiving ambient))
      (answerSame : ScopedPorts.eraseType data.answer = input.port)
      (tail : Pending globals outward world outsideAllowed ambient stack input output context) :
      PhasePending globals outward world requests ambient
        (.push (.running data savedCode closed) stack) .unit output (Context.normal context)

/-- Registration retains the whole original Site and its exact two original
source derivations, their private plans/rows, both contextual certificates and
the SAME executable root. It is not a successor Site for the armed stack. -/
structure RegistrationBodyProjection {receiving : SourceDependencyCapture.Scope}
    {hints : ReturnHints receiving} {context : Context hints}
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.cleanup action body) runtimeScope stack output final context root) where
  requests : List Instance
  latent : Footprint
  callbackDependencies : Dependencies
  callbackPlan : Plan callbackDependencies
  callbackRows : Rows (signature callbackPlan)
  callbackDemand : List Nat
  callbackRequirements : RecursiveRequirements.Requirements callbackDemand
  actualCallbackDependencies : Dependencies
  actualCallbackPlan : Plan actualCallbackDependencies
  actualCallbackRows : Rows (signature actualCallbackPlan)
  bodyDemand : List Nat
  bodyRequirements : RecursiveRequirements.Requirements bodyDemand
  bodyDependencies : Dependencies
  bodyPlan : Plan bodyDependencies
  bodyRows : Rows (signature bodyPlan)
  callback : Source globals outward world allowed runtimeScope Environment.empty action
    (Contract.function .unit .unit requests latent callbackPlan callbackRows)
    callbackDemand callbackRequirements actualCallbackPlan actualCallbackRows
  bodySource : Source globals outward world allowed runtimeScope Environment.empty body output
    bodyDemand bodyRequirements bodyPlan bodyRows
  admitted : requests ⊆ allowed
  certified : Certified outward world callbackPlan
  original : HEq site.current.source (IndexedSource.cleanup callback bodySource admitted certified)
  lexical : CoreCallableReceiverRefinement.LexicalBounds
  lexicalEmpty : lexical.environment = ScopedPorts.Support.empty
  callbackAuthentication : Authenticated globals.registry outward callback lexical (actualReceiver world receiving ambient)
  bodyAuthentication : Authenticated globals.registry outward bodySource lexical (actualReceiver world receiving ambient)
  bodyCertificate : SourceAdmission.Code outward actions budget phases world installations bodyRows
    (Context.cleanup (needs := requests) latent callbackRows context)
  callbackCertificate : SourceAdmission.Code outward actions budget phases world installations callbackRows
    (Context.normal context)
  bodyChecked : InstallationSupport.CodeChecked ambient outward bodyCertificate
  callbackChecked : InstallationSupport.CodeChecked ambient outward callbackCertificate
  bodyRun : Accounting.Run world installations bodyRows
    (Context.cleanup (needs := requests) latent callbackRows context) root

/-- This producer decomposes only the SAME current constructor and checks. It
executes no checker and accepts no desired body result, future Site or success. -/
theorem registration_body_projection {receiving : SourceDependencyCapture.Scope}
    {hints : ReturnHints receiving} {context : Context hints}
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.cleanup action body) runtimeScope stack output final context root)
    (closed : ClosedValue action) : Nonempty (RegistrationBodyProjection site) := by
  rcases site with ⟨sourceDemand, requirements, dependencies, plan, rows, bound, current,
    received, certificate, certificateChecked, pending, retained, retainedChecked,
    accounting, annotated, row, annotation, checked, bounded⟩
  obtain ⟨lexical, sameEnvironment, authentication⟩ := current.authentication
  cases authentication with
  | checked currentSupport hereditary =>
    cases hereditary with
    | cleanup callbackAuthentication bodyAuthentication =>
      rename_i certified admitted callbackSource bodySource
      obtain ⟨bodyCertificate, callbackCertificate, bodyChecked, callbackChecked, bodyRun⟩ :=
        normal_registration_checks callbackSource closed certificate certificateChecked accounting
      exact ⟨{
        requests := _, latent := _, callbackDependencies := _, callbackPlan := _, callbackRows := _,
        callbackDemand := _, callbackRequirements := _, actualCallbackDependencies := _,
        actualCallbackPlan := _, actualCallbackRows := _, bodyDemand := _, bodyRequirements := _,
        bodyDependencies := _, bodyPlan := _, bodyRows := _, callback := callbackSource,
        bodySource := bodySource, admitted := admitted, certified := certified, original := HEq.rfl,
        lexical := lexical, lexicalEmpty := sameEnvironment,
        callbackAuthentication := callbackAuthentication, bodyAuthentication := bodyAuthentication,
        bodyCertificate := bodyCertificate, callbackCertificate := callbackCertificate,
        bodyChecked := bodyChecked, callbackChecked := callbackChecked, bodyRun := bodyRun }⟩

/-- The current full callback/body annotations select canonical proof metadata.
The entire original Pending is embedded unchanged below the new armed position;
no annotation-alignment guard is delegated to a caller. -/
theorem RegistrationBodyProjection.armed_pending
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    {input : CleanupInput endpoint}
    {site : Site globals outward world allowed actions phases budget ambient installations
      (.cleanup input.data.action input.bodyCode) input.data.scope endpoint.lexical output final context root}
    (parts : RegistrationBodyProjection site) :
    PhasePending globals outward world allowed ambient
      (.push (.armed (CleanupInput.with_annotation input (runtimeType output) parts.requests).data) endpoint.lexical)
      output final (Context.cleanup (needs := parts.requests) parts.latent parts.callbackRows context) :=
  .armed parts.callback ⟨parts.lexical, parts.callbackAuthentication⟩ parts.certified
    rfl (runtimeType_port output) site.pending

/-- A current full saved-value facet constructs the bounded running pending
position at canonical answer annotation. The actual current ValueRel supplies
closedness; the exact rich saved Source and old Pending supply full authority. -/
theorem FullSavedValueAuthority.running_pending
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    {data : ActionData}
    {site : Site globals outward world allowed actions phases budget ambient installations
      value data.scope stack result final context root}
    {related : CoreValueRelation.ValueRel graph endpoint.owners endpoint.state.heap runtimeValue value}
    {registration : Site globals outward world allowed actions phases budget ambient installations
      (.cleanup data.action bodyCode) data.scope stack result final context root}
    (parts : RegistrationBodyProjection registration)
    (saved : FullSavedValueAuthority site related) :
    PhasePending globals outward world parts.requests ambient
      (.push (.running {data with answer := runtimeType result, requests := parts.requests}
        value related.closed) stack) .unit final (Context.normal context) :=
  .running (data := {data with answer := runtimeType result, requests := parts.requests})
    (input := result) parts.callback ⟨parts.lexical, parts.callbackAuthentication⟩ parts.certified rfl
    related.closed saved.source (by
      obtain ⟨lexical, _empty, authenticated⟩ := saved.authentication
      exact ⟨lexical, authenticated⟩) (runtimeType_port result) site.pending

omit evidence in
/-- A precise erasure boundary: arbitrary latent/private plans have the same
runtime type. The running receipt's answerTy therefore cannot select a full
saved-result Source or its private function body from runtime typing alone. -/
theorem runtime_type_erases_function_latent
    {input output : Contract} {requests : List Instance} {firstLatent secondLatent : Footprint}
    {firstDependencies secondDependencies : Dependencies}
    (firstPlan : Plan firstDependencies) (secondPlan : Plan secondDependencies)
    (firstRows : Rows (signature firstPlan)) (secondRows : Rows (signature secondPlan)) :
    runtimeType (Contract.function input output requests firstLatent firstPlan firstRows) =
      runtimeType (Contract.function input output requests secondLatent secondPlan secondRows) := rfl

end
#check CleanupInput.with_annotation
#check cleanup_annotation_state
#check FullSavedValueAuthority
#check full_saved_value_authority
#check PhasePending
#check RegistrationBodyProjection
#check registration_body_projection
#print axioms cleanup_annotation_state
#print axioms cleanup_annotation_actual
#print axioms normal_start_annotation_state
#print axioms normal_finish_annotation_state
#print axioms full_saved_value_authority
#print axioms FullSavedValueAuthority.pending
#print axioms registration_body_projection
#print axioms RegistrationBodyProjection.armed_pending
#print axioms FullSavedValueAuthority.running_pending
#print axioms runtime_type_erases_function_latent


section
variable [evidence : DeclarationPolicy]
open RecursiveRequirements (Requirements Checked)
open SourceDependencyAnnotations (RowAnnotation)
open SourceScheduledCleanupInterfaces.Lexical.Recursive (annotateDisposals)
open CoreCallableRichBetaPreservation (Selected actualCall)
open CoreCallableReceiverRefinement (LexicalBounds)
open CoreCallableRichBranchCurrentOrigins (OriginalArm RootSelection select_left select_right)

/-- The accepted Site fields are retained verbatim, replacing only its pending
field by the three-case additive PhasePending. No checker or source grammar is
introduced. Existing current receipts embed with all their fields unchanged. -/
structure PhaseSite (globals : Globals) (outward : List Instance) (world : List Nat) (allowed : List Instance)
    (actions : Syntax.UsageTickets) (phases : OwnerPhaseTransitions.Phases) (budget : Footprint)
    (ambient installations : List Nat) (expression : Code) (runtimeScope : Execution.Scope) (stack : Stack)
    (result final : Contract) {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving}
    (context : Context hints) (root : Requirements rootDemand) where
  sourceDemand : List Nat
  requirements : Requirements sourceDemand
  dependencies : Dependencies
  plan : Plan dependencies
  rows : Rows (signature plan)
  bound : List Nat
  current : CoreCallableContractAdmission.Supported globals outward
    world allowed runtimeScope
    Environment.empty ScopedPorts.Support.empty expression result sourceDemand requirements plan rows bound (actualReceiver world receiving ambient)
  received : bound ⊆ receiving.visibleResources ++ ambient
  certificate : SourceAdmission.Code outward actions budget phases
    world installations rows context
  certificateChecked : InstallationSupport.CodeChecked ambient outward certificate
  pending : PhasePending globals outward world allowed ambient stack result final context
  retained : SourceAdmission.Pending outward actions budget phases
    world installations context .nil .ordinary .ordinary
  retainedChecked : InstallationSupport.PendingChecked ambient outward retained
  accounting : Accounting.Run
    world installations rows context root
  annotated : Requirements rootDemand
  row : Footprint
  annotation : RowAnnotation root annotated
  checked : Checked [] [] phases (annotateDisposals annotated) row
  bounded : row ⊆ budget


def PhaseSite.of_site
    (site : Site globals outward world allowed actions phases budget ambient installations
      expression runtimeScope stack result final context root) :
    PhaseSite globals outward world allowed actions phases budget ambient installations
      expression runtimeScope stack result final context root := {
  sourceDemand := site.sourceDemand, requirements := site.requirements,
  dependencies := site.dependencies, plan := site.plan, rows := site.rows, bound := site.bound,
  current := site.current, received := site.received,
  certificate := site.certificate, certificateChecked := site.certificateChecked,
  pending := .original site.pending, retained := site.retained, retainedChecked := site.retainedChecked,
  accounting := site.accounting, annotated := site.annotated, row := site.row,
  annotation := site.annotation, checked := site.checked, bounded := site.bounded }

/-- Both retained lower witnesses are CURRENT outputs from the same callback
certificate. This is the accepted registration equation, not a future premise. -/
theorem RegistrationBodyProjection.body_retained
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    {site : Site globals outward world allowed actions phases budget ambient installations
      (.cleanup action body) runtimeScope stack output final context root}
    (parts : RegistrationBodyProjection site) :
    ∃ retained : SourceAdmission.Pending outward actions budget phases world installations
        (Context.cleanup (needs := parts.requests) parts.latent parts.callbackRows context)
        Context.nil .ordinary .ordinary,
      InstallationSupport.PendingChecked ambient outward retained := by
  let sameNormal := congrArg (fun p : Packed => (Context.normal p.context).pack)
    context.append_nil_pack.symm
  let callbackAtNil := parts.callbackCertificate.reindex_context sameNormal
  exact ⟨SourceAdmission.Pending.cleanup callbackAtNil site.retained,
    InstallationSupport.PendingChecked.cleanup
      (parts.callbackChecked.reindex_context sameNormal) site.retainedChecked⟩

/-- Normal callback retention is also computed from the whole same current
registration receipt; no caller supplies a future normal pending derivation. -/
theorem RegistrationBodyProjection.normal_retained
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    {site : Site globals outward world allowed actions phases budget ambient installations
      (.cleanup action body) runtimeScope stack output final context root}
    (parts : RegistrationBodyProjection site) :
    ∃ retained : SourceAdmission.Pending outward actions budget phases world installations
        (Context.normal context) Context.nil .ordinary .ordinary,
      InstallationSupport.PendingChecked ambient outward retained := by
  cases parts
  exact ⟨SourceAdmission.Pending.normal site.retained,
    InstallationSupport.PendingChecked.normal site.retainedChecked⟩

/-- The SAME current registration produces body authority at its actual armed
position. All old source/check/root fields remain at their original full result
Contract; lower retained proof terms are derived rather than supplied. -/
def RegistrationBodyProjection.body_phase
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    {input : CleanupInput endpoint}
    {site : Site globals outward world allowed actions phases budget ambient installations
      (.cleanup input.data.action input.bodyCode) input.data.scope endpoint.lexical output final context root}
    (parts : RegistrationBodyProjection site) :
    PhaseSite globals outward world allowed actions phases budget ambient installations
      input.bodyCode input.data.scope
      (.push (.armed (CleanupInput.with_annotation input (runtimeType output) parts.requests).data) endpoint.lexical)
      output final (Context.cleanup (needs := parts.requests) parts.latent parts.callbackRows context) root := by
  let receiver := actualReceiver world receiving ambient
  let sameNormal := congrArg (fun p : Packed => (Context.normal p.context).pack)
    context.append_nil_pack.symm
  let callbackAtNil := parts.callbackCertificate.reindex_context sameNormal
  let retained : SourceAdmission.Pending outward actions budget phases world installations
      (Context.cleanup (needs := parts.requests) parts.latent parts.callbackRows context)
      Context.nil .ordinary .ordinary :=
    SourceAdmission.Pending.cleanup callbackAtNil site.retained
  have retainedChecked : InstallationSupport.PendingChecked ambient outward retained :=
    .cleanup (parts.callbackChecked.reindex_context sameNormal) site.retainedChecked
  exact {
    sourceDemand := parts.bodyDemand, requirements := parts.bodyRequirements,
    dependencies := parts.bodyDependencies, plan := parts.bodyPlan, rows := parts.bodyRows,
    bound := receiver,
    current := ⟨parts.bodySource, by simpa only [parts.lexicalEmpty] using parts.bodyAuthentication.current_support,
      actualReceiver.issued, ⟨parts.lexical,parts.lexicalEmpty,parts.bodyAuthentication⟩,actualReceiver.issued⟩,
    received := actualReceiver.received, certificate := parts.bodyCertificate,
    certificateChecked := parts.bodyChecked, pending := parts.armed_pending,
    retained := retained, retainedChecked := retainedChecked, accounting := parts.bodyRun,
    annotated := site.annotated, row := site.row, annotation := site.annotation,
    checked := site.checked, bounded := site.bounded }

structure PhaseBetaPreserved
    {rootDemand : List Nat} {root : Requirements rootDemand}
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    (site : PhaseSite globals outward world allowed actions phases budget ambient installations
      (.app (.lambda parameter body) value) runtimeScope stack output final context root) where
  input : Contract
  requests : List Instance
  latent : Footprint
  publicDependencies : Dependencies
  publicPlan : Plan publicDependencies
  publicRows : Rows (signature publicPlan)
  functionDemand : List Nat
  functionRequirements : Requirements functionDemand
  functionDependencies : Dependencies
  functionPlan : Plan functionDependencies
  functionRows : Rows (signature functionPlan)
  originalFunction : Source globals outward world allowed runtimeScope Environment.empty
    (.lambda parameter body) (.function input output requests latent publicPlan publicRows)
    functionDemand functionRequirements functionPlan functionRows
  argumentDemand : List Nat
  argumentRequirements : Requirements argumentDemand
  argumentDependencies : Dependencies
  argumentPlan : Plan argumentDependencies
  argumentRows : Rows (signature argumentPlan)
  originalArgument : Source globals outward world allowed runtimeScope Environment.empty value input
    argumentDemand argumentRequirements argumentPlan argumentRows
  admitted : requests ⊆ allowed
  publicCertified : SourcePlannedChecks.Certified outward world publicPlan
  sameApplication : HEq (IndexedSource.app originalFunction originalArgument admitted publicCertified) site.current.source
  functionSource : Source globals outward world allowed runtimeScope Environment.empty
    (.lambda parameter body) (.function input output requests latent publicPlan publicRows)
    [] (.request [] []) .pure Rows.pure
  functionSummary : functionSource = IndexedSource.value_summary originalFunction (by trivial)
  lexical : LexicalBounds
  sameEnvironment : lexical.environment = ScopedPorts.Support.empty
  valueReceived : ScopedPorts.Support.evaluate ScopedPorts.Support.empty value.dependencies ⊆ actualReceiver world receiving ambient
  selected : Selected functionSource lexical
    (actualCall world (actualReceiver world receiving ambient) value actualReceiver.issued valueReceived) value
  nextRoot : Requirements rootDemand
  rootTransport : CoreCallableRootRefinement.RootTransport root nextRoot
  next : PhaseSite globals outward world allowed actions phases budget ambient installations
    (body.subst parameter value) .none stack output final context nextRoot
  exactDemand : next.sourceDemand = selected.family.demand
  exactRequirements : HEq next.requirements selected.family.requirements
  exactPlan : HEq next.plan selected.nextPlan
  exactRows : HEq next.rows selected.nextRows

omit evidence in
private theorem transport_phase_beta_rows
    {first second : SourcePlanSignatures.Signature dependencies}
    {firstRows : Rows first} {secondRows : Rows second}
    (same : first = second) (sameRows : HEq firstRows secondRows)
    (certificate : SourceAdmission.Code outward actions budget phases world installations secondRows context)
    (checked : InstallationSupport.CodeChecked ambient outward certificate)
    (run : Accounting.Run world installations secondRows context root) :
    ∃ nextCertificate : SourceAdmission.Code outward actions budget phases world installations firstRows context,
      InstallationSupport.CodeChecked ambient outward nextCertificate ∧
      Accounting.Run world installations firstRows context root := by
  subst second
  cases eq_of_heq sameRows
  exact ⟨certificate, checked, run⟩

/-- Current rich beta preservation. The current Site is a preservation premise;
all selected private checking, successor source and root accounting are outputs. -/
theorem PhaseSite.beta {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    (stable : SubstitutionPolicyStable (evidence := evidence) outward)
    (site : PhaseSite globals outward world allowed actions phases budget ambient installations
      (.app (.lambda parameter body) value) runtimeScope stack output final context root)
    (closed : ClosedValue value) (closure : ClosedValue (.lambda parameter body)) :
    Nonempty (PhaseBetaPreserved site) ∧
      RawStep ⟨.app (.lambda parameter body) value, runtimeScope, stack⟩
        ⟨body.subst parameter value, .none, stack⟩ [] [] := by
  constructor
  · rcases site with ⟨sourceDemand, requirements, dependencies, plan, rows, bound, current, received, certificate, certificateChecked,
      pending, retained, retainedChecked, accounting, annotated, row, annotation, checked, bounded⟩
    obtain ⟨lexical, sameEnvironment, authenticated⟩ := current.authentication
    cases authenticated with
    | checked actualSupport hereditary =>
      cases hereditary with
      | app functionAuth argumentAuth =>
        rename_i input requests latent publicDependencies publicPlan publicRows functionDemand functionRequirements
          functionDependencies functionPlan functionRows argumentDemand argumentRequirements argumentDependencies
          argumentPlan argumentRows publicCertified admitted argumentSource functionSource
        let receiver := actualReceiver world receiving ambient
        let summarySource := IndexedSource.value_summary functionSource closure.1
        have functionSupported : CoreCallableContractAdmission.Supported globals outward world allowed runtimeScope
            Environment.empty ScopedPorts.Support.empty (.lambda parameter body)
            (.function input output requests latent publicPlan publicRows)
            [] (.request [] []) .pure Rows.pure receiver receiver :=
          ⟨summarySource, by simpa only [sameEnvironment] using functionAuth.current_support,
            actualReceiver.issued, ⟨lexical, sameEnvironment, functionAuth.value_summary closure.1⟩, actualReceiver.issued⟩
        have argumentSupported : CoreCallableContractAdmission.Supported globals outward world allowed runtimeScope
            Environment.empty ScopedPorts.Support.empty value input argumentDemand argumentRequirements argumentPlan argumentRows receiver receiver :=
          ⟨argumentSource, by simpa only [sameEnvironment] using argumentAuth.current_support,
            actualReceiver.issued, ⟨lexical, sameEnvironment, argumentAuth⟩, actualReceiver.issued⟩
        obtain ⟨selectedLexical, selectedEnvironment, ⟨selected⟩⟩ :=
          functionSupported.beta_at stable argumentSupported closed
        cases certificate with
        | sequence functionCertificate restCertificate =>
          cases restCertificate with
          | sequence argumentCertificate publicCertificate =>
            cases certificateChecked with
            | sequence functionChecked restChecked =>
              cases restChecked with
              | sequence argumentChecked publicChecked =>
                have publicRun := (Accounting.silent_prefix_iff (Source.value_silent argumentSource closed.1) argumentRows publicRows).mp
                  ((Accounting.silent_prefix_iff (Source.value_silent functionSource closure.1) functionRows
                    (CoreCallableContractSource.sequenceRows argumentRows publicRows)).mp accounting)
                have modeSame := retained.return_mode
                have selectedRetained : SourceAdmission.Pending outward actions budget phases world installations context .nil
                    .ordinary (hints.returnMode .ordinary) := by
                  simpa only [modeSame] using retained
                have selectedRetainedChecked : InstallationSupport.PendingChecked ambient outward selectedRetained := by
                  simpa only [modeSame] using retainedChecked
                let privateCertificate := selected.refinement.code outward actions budget phases world installations context selectedRetained publicCertificate
                have privateChecked := selected.refinement.checked ambient outward actions budget phases world installations context
                  selectedRetained publicCertificate
                  (SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mp
                    (selected.authentic.1 selectedLexical _ selected.known
                    (by simpa only [selectedEnvironment, actualCall] using functionSupported.actual_received)).current_support)
                  actualReceiver.issued actualReceiver.received selectedRetainedChecked publicChecked
                obtain ⟨nextRoot, privateRun, rootTransport⟩ := selected.refinement.accounting world installations context root publicRun
                obtain ⟨nextCertificate, nextChecked, nextRun⟩ := transport_phase_beta_rows selected.sameSignature selected.sameRows
                  privateCertificate privateChecked privateRun
                obtain ⟨nextAnnotated, nextRow, nextAnnotation, nextRootChecked, nextBounded⟩ :=
                  rootTransport.checked [] [] phases budget annotation checked bounded
                let next : PhaseSite globals outward world allowed actions phases budget ambient installations
                    (body.subst parameter value) .none stack output final context nextRoot :=
                  { sourceDemand := selected.family.demand, requirements := selected.family.requirements,
                    dependencies := selected.family.dependencies selectedLexical _, plan := selected.nextPlan, rows := selected.nextRows,
                    bound := receiver, current := selected.current.allowed_weaken admitted, received := actualReceiver.received,
                    certificate := nextCertificate, certificateChecked := nextChecked, pending := pending, retained := retained,
                    retainedChecked := retainedChecked, accounting := nextRun,
                    annotated := nextAnnotated, row := nextRow, annotation := nextAnnotation, checked := nextRootChecked, bounded := nextBounded }
                exact ⟨{
                  input := input, requests := requests, latent := latent, publicDependencies := publicDependencies,
                  publicPlan := publicPlan, publicRows := publicRows,
                  functionDemand := functionDemand, functionRequirements := functionRequirements,
                  functionDependencies := functionDependencies, functionPlan := functionPlan, functionRows := functionRows,
                  originalFunction := functionSource, argumentDemand := argumentDemand,
                  argumentRequirements := argumentRequirements, argumentDependencies := argumentDependencies,
                  argumentPlan := argumentPlan, argumentRows := argumentRows, originalArgument := argumentSource,
                  admitted := admitted, publicCertified := publicCertified, sameApplication := HEq.rfl,
                  functionSource := summarySource, functionSummary := rfl,
                  lexical := selectedLexical, sameEnvironment := selectedEnvironment,
                  valueReceived := argumentSupported.actual_received, selected := selected,
                  nextRoot := nextRoot, rootTransport := rootTransport, next := next,
                  exactDemand := rfl, exactRequirements := HEq.rfl, exactPlan := HEq.rfl, exactRows := HEq.rfl }⟩
  · exact .beta parameter body value runtimeScope stack closed closure


structure PhaseBranchPreserved
    (site : PhaseSite globals outward world allowed actions phases budget ambient installations
      (.branch (.boolean choice) yes no) runtimeScope stack output final context root) where
  selectedDemand : List Nat
  selectedRoot : Requirements selectedDemand
  rootSelection : RootSelection root selectedRoot
  next : PhaseSite globals outward world allowed actions phases budget ambient installations
    (if choice then yes else no) runtimeScope stack output final context selectedRoot
  original : OriginalArm site.current.source next.current.source
  pending : next.pending = site.pending
  retained : next.retained = site.retained

/-- Project the actual chosen original arm, private checking and accounting.
Neither arm's body or full Contract is restricted to values or pure plans. -/
theorem PhaseSite.branch
    (site : PhaseSite globals outward world allowed actions phases budget ambient installations
      (.branch (.boolean choice) yes no) runtimeScope stack output final context root) :
    Nonempty (PhaseBranchPreserved site) := by
  rcases site with ⟨sourceDemand,requirements,dependencies,plan,rows,bound,current,received,
    certificate,certificateChecked,pending,retained,retainedChecked,accounting,annotated,row,annotation,checked,bounded⟩
  obtain ⟨lexical,sameEnvironment,authentication⟩ := current.authentication
  cases authentication with
  | checked currentSupport hereditary =>
    cases hereditary with
    | branch conditionAuth yesAuth noAuth =>
      rename_i sameDemand conditionSource yesSource noSource
      cases conditionSource
      have branchRun := (Accounting.silent_prefix_iff .pure Rows.pure _).mp accounting
      cases branchRun with
      | choice leftRun rightRun permutation =>
        rename_i secondDemand secondRoot firstRoot
        cases certificate with
        | sequence conditionCertificate branchesCertificate =>
          cases branchesCertificate with
          | choice leftCertificate rightCertificate =>
            cases certificateChecked with
            | sequence conditionChecked branchesChecked =>
              cases branchesChecked with
              | choice leftChecked rightChecked =>
                cases choice
                · have selection := select_right firstRoot secondRoot permutation
                  obtain ⟨nextAnnotated,nextRow,nextAnnotation,nextCheck,nextBound⟩ :=
                    selection.checked [] [] phases budget annotation checked bounded
                  let next : PhaseSite globals outward world allowed actions phases budget ambient installations
                      no runtimeScope stack output final context _ := {
                    sourceDemand := _,requirements := _,dependencies := _,plan := _,rows := _,
                    bound := actualReceiver world _ ambient,
                    current := ⟨noSource,by simpa only [sameEnvironment] using noAuth.current_support,
                      actualReceiver.issued,⟨lexical,sameEnvironment,noAuth⟩,current.receiverIssued⟩,
                    received := actualReceiver.received,certificate := rightCertificate,certificateChecked := rightChecked,
                    pending := pending,retained := retained,retainedChecked := retainedChecked,accounting := rightRun,
                    annotated := nextAnnotated,row := nextRow,annotation := nextAnnotation,checked := nextCheck,bounded := nextBound }
                  exact ⟨⟨_,_,selection,next,.no .boolean yesSource noSource sameDemand,rfl,rfl⟩⟩
                · have selection := select_left firstRoot secondRoot permutation
                  obtain ⟨nextAnnotated,nextRow,nextAnnotation,nextCheck,nextBound⟩ :=
                    selection.checked [] [] phases budget annotation checked bounded
                  let next : PhaseSite globals outward world allowed actions phases budget ambient installations
                      yes runtimeScope stack output final context _ := {
                    sourceDemand := _,requirements := _,dependencies := _,plan := _,rows := _,
                    bound := actualReceiver world _ ambient,
                    current := ⟨yesSource,by simpa only [sameEnvironment] using yesAuth.current_support,
                      actualReceiver.issued,⟨lexical,sameEnvironment,yesAuth⟩,current.receiverIssued⟩,
                    received := actualReceiver.received,certificate := leftCertificate,certificateChecked := leftChecked,
                    pending := pending,retained := retained,retainedChecked := retainedChecked,accounting := leftRun,
                    annotated := nextAnnotated,row := nextRow,annotation := nextAnnotation,checked := nextCheck,bounded := nextBound }
                  exact ⟨⟨_,_,selection,next,.yes .boolean yesSource noSource sameDemand,rfl,rfl⟩⟩


/-- The complete saved Contract is summarized only from current PhaseSite
Source/Auth, never from a runtime Ty. Its same PhasePending and original root
are retained at this current value completion. -/
structure PhaseSavedValueAuthority
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    (site : PhaseSite globals outward world allowed actions phases budget ambient installations
      value runtimeScope stack result final context root)
    (related : CoreValueRelation.ValueRel graph endpoint.owners endpoint.state.heap runtimeValue value) : Prop where
  source : Source globals outward world allowed runtimeScope Environment.empty value result
    [] (.request [] []) .pure Rows.pure
  original : source = IndexedSource.value_summary site.current.source related.closed.1
  authentication : ∃ lexical : LexicalBounds,
    lexical.environment = ScopedPorts.Support.empty ∧
    Authenticated globals.registry outward source lexical (actualReceiver world receiving ambient)
  certificate : SourceAdmission.Code outward actions budget phases world installations Rows.pure context
  certificateChecked : InstallationSupport.CodeChecked ambient outward certificate
  waiting : Accounting.Wait world installations context .ordinary root

/-- Reuses the same Pending-free normal_saved_value proof kernel with current
phase source/authentication and actual current ValueRel. -/
theorem PhaseSite.saved_value
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    (site : PhaseSite globals outward world allowed actions phases budget ambient installations
      value runtimeScope stack result final context root)
    (related : CoreValueRelation.ValueRel graph endpoint.owners endpoint.state.heap runtimeValue value) :
    PhaseSavedValueAuthority site related := by
  let summary := IndexedSource.value_summary site.current.source related.closed.1
  obtain ⟨lexical, sameEnvironment, authenticated⟩ := site.current.authentication
  obtain ⟨summaryAuth, waiting⟩ := normal_saved_value site.current.source authenticated related.closed site.accounting
  exact ⟨summary,rfl,⟨lexical,sameEnvironment,summaryAuth⟩,.pure,.pure,waiting⟩

open CoreCallableInitialAdmission (Program)
open CoreCallableRichAdmittedCurrentOrigins (Current)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation (RawTrace)

/-- Current phase authority keeps the original Program, actual Core prefix and
whole target ledger. The cleanup counter bound is a lifetime current invariant;
registration derives its allocating freshness from it, never from a fresh key
premise. It is constructed at the literal seed and preserved by named edges. -/
structure PhaseCurrent
    (program : Program initialGlobals initialActions initialBudget originalCode)
    (endpoint : Endpoint graph)
    (site : PhaseSite globals outward world allowed actions phases budget ambient installations
      expression runtimeScope stack result final context root) where
  input : InitialInput graph originalCode
  related : endpoint.point.machine = .eval ⟨expression,runtimeScope,stack⟩
  coreCount : Nat
  core : CoreAllocationHistory.Steps graph coreCount (CoreMachine.initial graph) endpoint.state
  run : LexicalUnwind.RunState
  machine : run.machine = endpoint.point.machine
  eventCount : Nat
  past : RawTrace ⟨.eval ⟨originalCode,.none,.nil⟩,[],[]⟩ eventCount run
  ledger : Ledger run.erase
  cleanupBound : ∀ identity, Owner.cleanup identity ∈ run.issued → identity < endpoint.state.nextCleanup

/-- This bridge consumes only current causal facts missing from the accepted
Current interface. No future Site, step success or fresh identity is required. -/
def PhaseCurrent.of_current
    {site : Site globals outward world allowed actions phases budget ambient installations
      expression runtimeScope stack result final context root}
    (current : Current program endpoint site)
    (core : CoreAllocationHistory.Steps graph count (CoreMachine.initial graph) endpoint.state)
    (cleanupBound : ∀ identity, Owner.cleanup identity ∈ current.run.issued → identity < endpoint.state.nextCleanup) :
    PhaseCurrent program endpoint (PhaseSite.of_site site) := {
  input := current.input, related := current.related.machine,
  coreCount := count, core := core, run := current.run, machine := current.machine,
  eventCount := current.eventCount, past := current.past, ledger := current.ledger,
  cleanupBound := cleanupBound }

/-- The stronger phase receipt is inhabited directly at original admission.
No historical counter invariant is delegated to the initial caller. -/
noncomputable def phase_initial
    (program : Program globals actions budget code) (input : InitialInput graph code) :
    PhaseCurrent program (initial_endpoint input) (PhaseSite.of_site program.site) := {
  input := input, related := rfl, coreCount := 0, core := .refl _,
  run := ⟨.eval ⟨code,.none,.nil⟩,[],[]⟩, machine := rfl,
  eventCount := 0, past := .refl,
  ledger := ⟨List.Perm.refl [],List.nodup_nil⟩,
  cleanupBound := by intro identity impossible; cases impossible }

/-- Allocating cleanup freshness follows from current lifetime issuance and
actual nextCleanup. Tickets and cleanup identities remain different Owner cases. -/
theorem PhaseCurrent.cleanup_fresh
    (current : PhaseCurrent program endpoint site) :
    (current.run.issued ++ [Owner.cleanup endpoint.state.nextCleanup]).Nodup := by
  have unique : current.run.issued.Nodup := by
    simpa only [LexicalUnwind.RunState.erase] using current.ledger.2
  have absent : Owner.cleanup endpoint.state.nextCleanup ∉ current.run.issued := by
    intro member
    exact Nat.lt_irrefl _ (current.cleanupBound _ member)
  refine List.nodup_append.mpr ⟨unique, by simp, ?_⟩
  intro old member new inserted same
  have identity : new = Owner.cleanup endpoint.state.nextCleanup := by simpa using inserted
  apply absent
  simpa only [same,identity] using member

/-- The full callback/body decomposition, canonical armed PhaseSite and actual
registration endpoint are outputs of the same current receipt. The entire
original result Contract, private plans/rows and root stay in parts.body_phase. -/
structure PhaseRegistrationEvent
    (input : CleanupInput endpoint)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.cleanup input.data.action input.bodyCode) input.data.scope endpoint.lexical output final context root)
    (current : PhaseCurrent program endpoint (PhaseSite.of_site site)) where
  parts : RegistrationBodyProjection site
  after : PhaseCurrent program
    (cleanup_result (CleanupInput.with_annotation input (runtimeType output) parts.requests)).after
    (parts.body_phase (input := input))
  event : LexicalUnwind.Event current.run after.run
  issued : after.run.issued = current.run.issued ++ [Owner.cleanup input.data.identity]
  completed : after.run.completed = current.run.completed
  count : after.eventCount = current.eventCount + 1
  sameCore : (cleanup_result (CleanupInput.with_annotation input (runtimeType output) parts.requests)).after.state =
    (cleanup_result input).after.state
  actual : CoreMachine.next graph endpoint.state = .stepped (cleanup_result input).after.state
  positive : CoreUnwindRelation.Positive endpoint.point.machine
    (cleanup_result (CleanupInput.with_annotation input (runtimeType output) parts.requests)).after.point.machine
    [.cleanup input.data.identity] []
  ownership : CurrentOwnership graph endpoint.owners
    (cleanup_result (CleanupInput.with_annotation input (runtimeType output) parts.requests)).after.state
    input.data.scope (cleanup_result (CleanupInput.with_annotation input (runtimeType output) parts.requests)).after.lexical

/-- Register the actual body, retaining old Pending below armed and deriving
checks/root/full source authority from the whole current registration Site. -/
theorem phase_registration_event
    (input : CleanupInput endpoint)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.cleanup input.data.action input.bodyCode) input.data.scope endpoint.lexical output final context root)
    (current : PhaseCurrent program endpoint (PhaseSite.of_site site)) :
    Nonempty (PhaseRegistrationEvent input site current) := by
  obtain ⟨parts⟩ := registration_body_projection site input.data.closed
  let canonical := CleanupInput.with_annotation input (runtimeType output) parts.requests
  let nextSite := parts.body_phase (input := input)
  have related : (cleanup_result canonical).after.point.machine =
      .eval ⟨input.bodyCode,input.data.scope,
        .push (.armed canonical.data) endpoint.lexical⟩ := rfl
  let run : LexicalUnwind.RunState :=
    ⟨(cleanup_result canonical).after.point.machine,
      current.run.issued ++ [Owner.cleanup input.data.identity],current.run.completed⟩
  have transition : LexicalUnwind.Transition current.run.machine run.machine
      [.cleanup input.data.identity] [] := by
    change LexicalUnwind.Transition current.run.machine (cleanup_result canonical).after.point.machine
      [.cleanup input.data.identity] []
    rw [current.machine,current.related,related]
    exact .evaluate (cleanup_data canonical).raw (by trivial)
  have fresh : (current.run.issued ++ [Owner.cleanup input.data.identity]).Nodup := by
    rw [input.identity]
    exact current.cleanup_fresh
  have event : LexicalUnwind.Event current.run run := by
    simpa only [List.nil_append] using LexicalUnwind.Event.step transition fresh
  have cleanupBound : ∀ identity, Owner.cleanup identity ∈ run.issued →
      identity < (cleanup_result canonical).after.state.nextCleanup := by
    intro identity member
    change Owner.cleanup identity ∈ current.run.issued ++ [Owner.cleanup input.data.identity] at member
    change identity < endpoint.state.nextCleanup + 1
    rcases List.mem_append.mp member with old | allocated
    · exact Nat.lt_trans (current.cleanupBound identity old) (Nat.lt_succ_self _)
    · have same : identity = input.data.identity := by
        have sameOwner : Owner.cleanup identity = Owner.cleanup input.data.identity := by simpa using allocated
        exact Owner.cleanup.inj sameOwner
      rw [same,input.identity]
      exact Nat.lt_succ_self _
  let after : PhaseCurrent program (cleanup_result canonical).after nextSite := {
    input := current.input, related := related,
    coreCount := current.coreCount + 1, core := .snoc current.core (cleanup_result canonical).core,
    run := run, machine := rfl, eventCount := current.eventCount + 1,
    past := .step current.past event, ledger := LexicalUnwind.event_preserves_ledger event current.ledger,
    cleanupBound := cleanupBound }
  have positive : CoreUnwindRelation.Positive endpoint.point.machine
      (cleanup_result canonical).after.point.machine [.cleanup input.data.identity] [] := by
    rw [current.related,related]
    exact .one (.evaluate (cleanup_data canonical).raw (by trivial))
  exact ⟨⟨parts,after,event,rfl,rfl,rfl,
    cleanup_annotation_state input (runtimeType output) parts.requests,
    (cleanup_result input).core,positive,cleanup_current_ownership canonical⟩⟩

/-- The actual event's complete inherited ledger yields endpoint ownership,
including no completed owner in the live stack. -/
theorem PhaseRegistrationEvent.endpoint_accounting
    (event : PhaseRegistrationEvent input site current) :
    Ledger event.after.run.erase ∧ event.after.run.completed.Nodup ∧
      (∀ owner, owner ∈ event.after.run.machine.stack.erase.owners → owner ∉ event.after.run.completed) :=
  event.after.past.ownership ⟨List.Perm.refl [],List.nodup_nil⟩

/-- Actual beta enters the full selected private family while carrying the
same phase pending and both causal histories. No successor identity is input. -/
structure PhaseBetaEvent
    (input : BetaInput endpoint)
    (site : PhaseSite globals outward world allowed actions phases budget ambient installations
      (.app (.lambda input.parameter input.bodyCode) input.argument) input.scope endpoint.lexical
      output final context root)
    (current : PhaseCurrent program endpoint site) where
  preserved : PhaseBetaPreserved site
  after : PhaseCurrent program (beta_result input).after preserved.next
  event : LexicalUnwind.Event current.run after.run
  issued : after.run.issued = current.run.issued
  completed : after.run.completed = current.run.completed
  count : after.eventCount = current.eventCount + 1
  actual : CoreMachine.next graph endpoint.state = .stepped (beta_result input).after.state
  matching : Matching graph endpoint (beta_result input).after [] []
  positive : CoreUnwindRelation.Positive endpoint.point.machine (beta_result input).after.point.machine [] []

/-- The accepted nonallocating beta event kernel applies to the phase carrier;
its current cleanup bound is preserved because actual beta keeps nextCleanup. -/
theorem phase_beta_event
    (stable : SubstitutionPolicyStable (evidence := evidence) outward)
    (input : BetaInput endpoint)
    (site : PhaseSite globals outward world allowed actions phases budget ambient installations
      (.app (.lambda input.parameter input.bodyCode) input.argument) input.scope endpoint.lexical
      output final context root)
    (current : PhaseCurrent program endpoint site) : Nonempty (PhaseBetaEvent input site current) := by
  obtain ⟨⟨preserved⟩,raw⟩ := site.beta stable input.operand.closed input.function.closed
  have related : (beta_result input).after.point.machine =
      .eval ⟨input.bodyCode.subst input.parameter input.argument,.none,endpoint.lexical⟩ := rfl
  let run : LexicalUnwind.RunState :=
    ⟨(beta_result input).after.point.machine,current.run.issued,current.run.completed⟩
  have transition : LexicalUnwind.Transition current.run.machine run.machine [] [] := by
    change LexicalUnwind.Transition current.run.machine (beta_result input).after.point.machine [] []
    rw [current.machine,current.related,related]
    exact .evaluate raw (by trivial)
  have fresh : (current.run.issued ++ []).Nodup := by
    simpa only [List.append_nil,LexicalUnwind.RunState.erase] using current.ledger.2
  have event : LexicalUnwind.Event current.run run := by
    simpa only [List.append_nil,List.nil_append] using LexicalUnwind.Event.step transition fresh
  let after : PhaseCurrent program (beta_result input).after preserved.next := {
    input := current.input, related := related,
    coreCount := current.coreCount + 1, core := .snoc current.core (beta_result input).core,
    run := run, machine := rfl, eventCount := current.eventCount + 1,
    past := .step current.past event, ledger := LexicalUnwind.event_preserves_ledger event current.ledger,
    cleanupBound := current.cleanupBound }
  have positive : CoreUnwindRelation.Positive endpoint.point.machine (beta_result input).after.point.machine [] [] := by
    rw [current.related,related]
    exact .one (.evaluate raw (by trivial))
  exact ⟨⟨preserved,after,event,rfl,rfl,rfl,
    (beta_result input).core,(beta_result input).matching,positive⟩⟩


open CoreCallableRichBranchCurrentOrigins (DecisionInput decision_result decision_focus)
open CoreValueRelation CoreStrictFrames CoreStrictStack

omit evidence in
/-- Reconstruct the same actual Boolean Core.next state and project its counter.
This is the decision provenance proof's deterministic state calculation; no
future counter equality or selected source premise is introduced. -/
theorem phase_decision_nextCleanup (input : DecisionInput endpoint) :
    (decision_result input).after.state.nextCleanup = endpoint.state.nextCleanup := by
  have computed := (decision_result input).core
  rcases input with ⟨choice,frame,plain,yesCode,noCode,position,related,control,maps,focus⟩
  change FrameRel graph endpoint.owners endpoint.state.heap frame plain.context at related
  rw [position] at related
  cases related with
  | booleanMatch yesTranslated noTranslated yesSaved noSaved =>
    rename_i yesFuel yes rawYes noFuel no rawNo environment reversed
    have shape : endpoint.state.frames =
        .matchCases (CoreStrictSteps.booleanArms yes no reversed) environment :: endpoint.physical := by
      simpa only [maps,framesOf,List.map_cons,List.map_nil,List.cons_append,List.nil_append] using endpoint.frames
    have actual : CoreMachine.next graph endpoint.state = .stepped
        { endpoint.state with
          control := .evaluate (if choice then yes else no) environment
          frames := endpoint.physical } := by
      simp only [CoreMachine.next,control,shape,CoreStrictSteps.select_boolean]
    have same := CoreMachine.Outcome.stepped.inj (computed.symm.trans actual)
    have counterSame := congrArg (fun state : CoreMachine.State => state.nextCleanup) same
    simpa only using counterSame

/-- The chosen original full arm, private plans/rows and selected root are the
same PhaseBranchPreserved outputs; the current lifetime ledger is inherited. -/
structure PhaseDecisionEvent
    (input : DecisionInput endpoint)
    (site : PhaseSite globals outward world allowed actions phases budget ambient installations
      (.branch (.boolean input.choice) input.yesCode input.noCode) input.plain.scope endpoint.lexical
      output final context root)
    (current : PhaseCurrent program endpoint site) where
  preserved : PhaseBranchPreserved site
  after : PhaseCurrent program (decision_result input).after preserved.next
  event : LexicalUnwind.Event current.run after.run
  issued : after.run.issued = current.run.issued
  completed : after.run.completed = current.run.completed
  count : after.eventCount = current.eventCount + 1
  actual : CoreMachine.next graph endpoint.state = .stepped (decision_result input).after.state
  matching : Matching graph endpoint (decision_result input).after [] []
  positive : CoreUnwindRelation.Positive endpoint.point.machine (decision_result input).after.point.machine [] []

/-- Both Boolean choices preserve current causal phase authority via the actual
accepted endpoint and nonallocating event kernel. The cleanup counter equality
is computed locally, not delegated to the caller. -/
theorem phase_decision_event
    (input : DecisionInput endpoint)
    (site : PhaseSite globals outward world allowed actions phases budget ambient installations
      (.branch (.boolean input.choice) input.yesCode input.noCode) input.plain.scope endpoint.lexical
      output final context root)
    (current : PhaseCurrent program endpoint site) : Nonempty (PhaseDecisionEvent input site current) := by
  obtain ⟨preserved⟩ := site.branch
  obtain ⟨focus,lexical,history,owners,heap,physical,maps⟩ := decision_focus input
  have related : (decision_result input).after.point.machine =
      .eval ⟨if input.choice then input.yesCode else input.noCode,input.plain.scope,endpoint.lexical⟩ := by
    simp only [Endpoint.point,focus,lexical,CoreCleanupRunFrames.attach,Stack.append]
  let run : LexicalUnwind.RunState :=
    ⟨(decision_result input).after.point.machine,current.run.issued,current.run.completed⟩
  have transition : LexicalUnwind.Transition current.run.machine run.machine [] [] := by
    change LexicalUnwind.Transition current.run.machine (decision_result input).after.point.machine [] []
    rw [current.machine,current.related,related]
    cases input.choice
    · exact .evaluate (.ifFalse _ _ _ _) (by trivial)
    · exact .evaluate (.ifTrue _ _ _ _) (by trivial)
  have fresh : (current.run.issued ++ []).Nodup := by
    simpa only [List.append_nil,LexicalUnwind.RunState.erase] using current.ledger.2
  have event : LexicalUnwind.Event current.run run := by
    simpa only [List.append_nil,List.nil_append] using LexicalUnwind.Event.step transition fresh
  have cleanupBound : ∀ identity, Owner.cleanup identity ∈ run.issued →
      identity < (decision_result input).after.state.nextCleanup := by
    intro identity member
    rw [phase_decision_nextCleanup input]
    exact current.cleanupBound identity member
  let after : PhaseCurrent program (decision_result input).after preserved.next := {
    input := current.input, related := related,
    coreCount := current.coreCount + 1, core := .snoc current.core (decision_result input).core,
    run := run, machine := rfl, eventCount := current.eventCount + 1,
    past := .step current.past event, ledger := LexicalUnwind.event_preserves_ledger event current.ledger,
    cleanupBound := cleanupBound }
  have positive : CoreUnwindRelation.Positive endpoint.point.machine (decision_result input).after.point.machine [] [] := by
    rw [current.related,related]
    cases input.choice
    · exact .one (.evaluate (.ifFalse _ _ _ _) (by trivial))
    · exact .one (.evaluate (.ifTrue _ _ _ _) (by trivial))
  exact ⟨⟨preserved,after,event,rfl,rfl,rfl,
    (decision_result input).core,(decision_result input).matching,positive⟩⟩


omit evidence in
/-- A closed current value's support is independent of lexical lookup. This
uses the existing dependency congruence and closed-value variable exclusion. -/
private theorem closed_phase_evaluation (closed : ClosedValue value)
    (first second : ScopedPorts.Support.Env) :
    ScopedPorts.Support.evaluate first value.dependencies =
      ScopedPorts.Support.evaluate second value.dependencies := by
  apply ScopedPorts.Support.evaluation_congr
  intro name member
  exact False.elim (ScopedTyping.closedValue_no_variable closed member)

omit evidence in
/-- Extract the current normal callback checks and retained lower continuation
from the SAME current armed retained derivation; no future normal witness is an
input. Context append-nil equality is transported explicitly. -/
theorem phase_cleanup_retained_parts
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    {callbackDependencies : Dependencies} {callbackPlan : Plan callbackDependencies}
    {callbackRows : Rows (signature callbackPlan)}
    (retained : SourceAdmission.Pending outward actions budget phases world installations
      (Context.cleanup (needs := requests) latent callbackRows context) Context.nil .ordinary .ordinary)
    (checked : InstallationSupport.PendingChecked ambient outward retained) :
    (∃ callback : SourceAdmission.Code outward actions budget phases world installations
        callbackRows (Context.normal context), InstallationSupport.CodeChecked ambient outward callback) ∧
    (∃ normal : SourceAdmission.Pending outward actions budget phases world installations
        (Context.normal context) Context.nil .ordinary .ordinary,
      InstallationSupport.PendingChecked ambient outward normal) := by
  cases retained with
  | cleanup callback tail =>
      cases checked with
      | cleanup callbackChecked tailChecked =>
          let sameNormal := congrArg (fun p : Packed => (Context.normal p.context).pack)
            context.append_nil_pack
          exact ⟨⟨callback.reindex_context sameNormal,callbackChecked.reindex_context sameNormal⟩,
            ⟨SourceAdmission.Pending.normal tail,InstallationSupport.PendingChecked.normal tailChecked⟩⟩

/-- This current output retains the full saved result Source/Auth at the armed
scope and the SAME ordinary Wait/root, alongside the generated normal callback
PhaseSite. It does not infer the saved Contract from the erased runtime answer. -/
structure PhaseCallbackAuthority
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    {callbackDependencies : Dependencies} {callbackPlan : Plan callbackDependencies}
    {callbackRows : Rows (signature callbackPlan)}
    (site : PhaseSite globals outward world allowed actions phases budget ambient installations
      value runtimeScope (.push (.armed data) stack) result final
      (Context.cleanup (needs := requests) latent callbackRows context) root)
    (related : CoreValueRelation.ValueRel graph endpoint.owners endpoint.state.heap runtimeValue value) where
  saved : PhaseSavedValueAuthority site related
  savedSource : Source globals outward world allowed data.scope Environment.empty value result
    [] (.request [] []) .pure Rows.pure
  savedSame : savedSource = IndexedSource.value_allowed saved.source related.closed.1 allowed data.scope
  savedAuthentication : ∃ lexical : LexicalBounds,
    Authenticated globals.registry outward savedSource lexical (actualReceiver world receiving ambient)
  next : PhaseSite globals outward world requests actions phases budget ambient installations
    (.app data.action .unit) .none (.push (.running data value related.closed) stack)
    .unit final (Context.normal context) root
  waiting : Accounting.Wait world installations
    (Context.cleanup (needs := requests) latent callbackRows context) .ordinary root

-- Generalize the stored signature so inversion retains the constructor-selected private plan.
private theorem phase_callback_next
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    {callbackDependencies : Dependencies}
    {callbackSignature : SourcePlanSignatures.Signature callbackDependencies}
    {callbackRows : Rows callbackSignature}
    (site : PhaseSite globals outward world allowed actions phases budget ambient installations
      value runtimeScope (.push (.armed data) stack) result final
      (Context.cleanup (needs := requests) latent callbackRows context) root)
    (related : CoreValueRelation.ValueRel graph endpoint.owners endpoint.state.heap runtimeValue value) :
    Nonempty (PhaseSite globals outward world requests actions phases budget ambient installations
      (.app data.action .unit) .none (.push (.running data value related.closed) stack)
      .unit final (Context.normal context) root) := by
  let saved := site.saved_value related
  let savedAtScope := IndexedSource.value_allowed saved.source related.closed.1 allowed data.scope
  obtain ⟨savedLexical,savedEnvironment,savedAuth⟩ := saved.authentication
  have savedAtAuth : Authenticated globals.registry outward savedAtScope savedLexical
      (actualReceiver world receiving ambient) :=
    savedAuth.value_allowed related.closed.1 allowed data.scope
  cases pendingSame : site.pending with
  | original pending => cases pending
  | armed callback authenticated certified requestsSame answerSame tail =>
      obtain ⟨⟨callbackCertificate,callbackChecked⟩,⟨normalRetained,normalRetainedChecked⟩⟩ :=
        phase_cleanup_retained_parts site.retained site.retainedChecked
      have callbackRun := cleanup_wait_callback saved.waiting
      obtain ⟨callbackLexical,callbackAuth⟩ := authenticated
      have callbackReceived : ScopedPorts.Support.evaluate ScopedPorts.Support.empty data.action.dependencies ⊆
          actualReceiver world receiving ambient := by
        rw [closed_phase_evaluation data.closed ScopedPorts.Support.empty callbackLexical.environment]
        exact SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mp
          callbackAuth.current_support
      let summary := IndexedSource.value_summary callback data.closed.1
      have summaryAuth : Authenticated globals.registry outward summary ([] : LexicalBounds)
          (actualReceiver world receiving ambient) := by
        apply (callbackAuth.value_summary data.closed.1).value_reauthenticate data.closed
        exact callbackReceived
      obtain ⟨applicationSource,applicationAuth,applicationCertificate,applicationChecked,applicationRun⟩ :=
        normal_callback_application summary summaryAuth data.closed certified
          callbackCertificate callbackChecked callbackRun
      let running : PhasePending globals outward world requests ambient
          (.push (.running data value related.closed) stack) .unit final (Context.normal context) :=
        .running callback ⟨callbackLexical,callbackAuth⟩ certified requestsSame related.closed
          savedAtScope ⟨savedLexical,savedAtAuth⟩ answerSame tail
      let next : PhaseSite globals outward world requests actions phases budget ambient installations
          (.app data.action .unit) .none (.push (.running data value related.closed) stack)
          .unit final (Context.normal context) root := {
        sourceDemand := [], requirements := _, dependencies := _, plan := _, rows := _,
        bound := actualReceiver world receiving ambient,
        current := ⟨applicationSource,applicationAuth.current_support,actualReceiver.issued,
          ⟨[],rfl,applicationAuth⟩,actualReceiver.issued⟩,
        received := actualReceiver.received, certificate := applicationCertificate,
        certificateChecked := applicationChecked, pending := running,
        retained := normalRetained, retainedChecked := normalRetainedChecked, accounting := applicationRun,
        annotated := site.annotated, row := site.row, annotation := site.annotation,
        checked := site.checked, bounded := site.bounded }
      exact ⟨next⟩

/-- Current armed pending, full saved value and derived lower callback checks
construct running pending and callback authority at the identical root. Only
current ValueRel is supplied; future Site/Pending/Source are outputs. -/
theorem phase_callback_authority
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    {callbackDependencies : Dependencies} {callbackPlan : Plan callbackDependencies}
    {callbackRows : Rows (signature callbackPlan)}
    (site : PhaseSite globals outward world allowed actions phases budget ambient installations
      value runtimeScope (.push (.armed data) stack) result final
      (Context.cleanup (needs := requests) latent callbackRows context) root)
    (related : CoreValueRelation.ValueRel graph endpoint.owners endpoint.state.heap runtimeValue value) :
    Nonempty (PhaseCallbackAuthority site related) := by
  let saved := site.saved_value related
  let savedAtScope := IndexedSource.value_allowed saved.source related.closed.1 allowed data.scope
  obtain ⟨savedLexical,savedEnvironment,savedAuth⟩ := saved.authentication
  have savedAtAuth : Authenticated globals.registry outward savedAtScope savedLexical
      (actualReceiver world receiving ambient) :=
    savedAuth.value_allowed related.closed.1 allowed data.scope
  obtain ⟨next⟩ := phase_callback_next site related
  exact ⟨⟨saved,savedAtScope,rfl,⟨savedLexical,savedAtAuth⟩,next,saved.waiting⟩⟩

omit evidence in
/-- Minimal CURRENT runtime head needed by the accepted normal-start producer.
No future endpoint or rich authority is stored. Automatic extraction from the
whole Endpoint.history and current ticket provenance remains a separate join. -/
structure CurrentArmedRuntime
    (endpoint : Endpoint graph) (data : ActionData) (stack : Stack)
    (runtimeValue : CoreMachine.Value) where
  cleanupOwners : CoreTranslation.OwnerMap
  action : Nat
  environment : CoreMachine.Environment
  physical : List CoreMachine.Frame
  returned : endpoint.state.control = .returned runtimeValue
  frames : endpoint.state.frames = .cleanupBoundary action environment data.identity :: physical
  installed : CoreCallableCleanupOrigins.SavedCleanupOrigin graph cleanupOwners endpoint.state.heap
    action environment data physical
  outside : GeneralHistory graph endpoint.state.heap physical stack
  bounded : TicketBound endpoint.state (.push (.armed data) stack)

/-- The exact current runtime head computes the accepted normal start and its
actual Core prefix. This interface does not pretend the missing head/provenance
inversion is already supplied by PhaseCurrent; all additional facts are current. -/
theorem phase_normal_start_runtime
    (site : PhaseSite globals outward world allowed actions phases budget ambient installations
      value runtimeScope (.push (.armed data) stack) result final context root)
    (current : PhaseCurrent program endpoint site)
    (related : CoreValueRelation.ValueRel graph endpoint.owners endpoint.state.heap runtimeValue value)
    (head : CurrentArmedRuntime endpoint data stack runtimeValue) :
    ∃ start : RunningStartPast graph head.cleanupOwners head.action head.environment data
        runtimeValue value head.physical stack,
      start.predecessor = endpoint.state ∧
      CoreMachine.next graph endpoint.state = .stepped (started start).state ∧
      CoreAllocationHistory.Steps graph (current.coreCount + 1)
        (CoreMachine.initial graph) (started start).state ∧
      (started start).state.nextCleanup = endpoint.state.nextCleanup := by
  obtain ⟨actual,_owned,running,sameInstalled,_history⟩ :=
    normal_start_history head.installed related head.outside head.bounded runtimeScope
  let start : RunningStartPast graph head.cleanupOwners head.action head.environment data
      runtimeValue value head.physical stack :=
    ⟨endpoint.state,endpoint.owners,runtimeScope,head.installed,related,head.outside,running,sameInstalled,actual⟩
  have same : CoreGeneralRestoration.returnedState endpoint.state runtimeValue
      (.cleanupBoundary head.action head.environment data.identity :: head.physical) = endpoint.state := by
    simp only [CoreGeneralRestoration.returnedState]
    rw [← head.returned,← head.frames]
  have core := actual.core
  rw [same] at core
  exact ⟨start,rfl,core,.snoc current.core core,rfl⟩


omit evidence in
/-- A current origin carrier retains exactly the provenance that a plain
GeneralHistory.push cleanup deliberately erases. It is produced at actual
registration, not reconstructed from a desired normal-start receipt. -/
structure ArmedOrigin (endpoint : Endpoint graph) (data : ActionData) (stack : Stack) where
  cleanupOwners : CoreTranslation.OwnerMap
  action : Nat
  environment : CoreMachine.Environment
  physical : List CoreMachine.Frame
  physicalSame : endpoint.physical = .cleanupBoundary action environment data.identity :: physical
  lexicalSame : endpoint.lexical = .push (.armed data) stack
  installed : CoreCallableCleanupOrigins.SavedCleanupOrigin graph cleanupOwners endpoint.state.heap
    action environment data physical
  outside : GeneralHistory graph endpoint.state.heap physical stack
  bounded : TicketBound endpoint.state (.push (.armed data) stack)

omit evidence in
/-- SAME actual registration retains its original full caller scope path and
outside history. The existing ownership producer supplies the current bound. -/
noncomputable def registration_armed_origin (input : CleanupInput endpoint) :
    ArmedOrigin (cleanup_result input).after input.data endpoint.lexical := {
  cleanupOwners := endpoint.owners, action := input.action, environment := input.environment,
  physical := endpoint.physical, physicalSame := rfl, lexicalSame := rfl,
  installed := (cleanup_data input).past.installed, outside := endpoint.history,
  bounded := (cleanup_current_ownership input).tickets }

omit evidence in
/-- Actual beta keeps current heap, lexical suffix, physical suffix and capture
observations. The whole original installed provenance is retained unchanged. -/
def ArmedOrigin.beta (origin : ArmedOrigin endpoint data stack) (input : BetaInput endpoint) :
    ArmedOrigin (beta_result input).after data stack := {
  cleanupOwners := origin.cleanupOwners, action := origin.action, environment := origin.environment,
  physical := origin.physical, physicalSame := origin.physicalSame, lexicalSame := origin.lexicalSame,
  installed := origin.installed, outside := origin.outside, bounded := origin.bounded }

omit evidence in
/-- The actual Boolean state calculation also preserves capture observations.
Its deterministic proof uses only current input, independently of rich source. -/
theorem phase_decision_observations (input : DecisionInput endpoint) :
    (decision_result input).after.state.observations = endpoint.state.observations := by
  have computed := (decision_result input).core
  rcases input with ⟨choice,frame,plain,yesCode,noCode,position,related,control,maps,focus⟩
  change FrameRel graph endpoint.owners endpoint.state.heap frame plain.context at related
  rw [position] at related
  cases related with
  | booleanMatch yesTranslated noTranslated yesSaved noSaved =>
    rename_i yesFuel yes rawYes noFuel no rawNo environment reversed
    have shape : endpoint.state.frames =
        .matchCases (CoreStrictSteps.booleanArms yes no reversed) environment :: endpoint.physical := by
      simpa only [maps,framesOf,List.map_cons,List.map_nil,List.cons_append,List.nil_append] using endpoint.frames
    have actual : CoreMachine.next graph endpoint.state = .stepped
        { endpoint.state with
          control := .evaluate (if choice then yes else no) environment
          frames := endpoint.physical } := by
      simp only [CoreMachine.next,control,shape,CoreStrictSteps.select_boolean]
    have same := CoreMachine.Outcome.stepped.inj (computed.symm.trans actual)
    have observationsSame := congrArg (fun state : CoreMachine.State => state.observations) same
    simpa only using observationsSame

omit evidence in
/-- The existing actual decision projections preserve the installed scope and
outside history; actual observations preserve the current ticket bound. -/
def ArmedOrigin.decision (origin : ArmedOrigin endpoint data stack) (input : DecisionInput endpoint) :
    ArmedOrigin (decision_result input).after data stack := by
  obtain ⟨_focus,lexical,_history,_owners,heap,physical,_maps⟩ := decision_focus input
  exact {
    cleanupOwners := origin.cleanupOwners, action := origin.action, environment := origin.environment,
    physical := origin.physical, physicalSame := physical.trans origin.physicalSame,
    lexicalSame := lexical.trans origin.lexicalSame,
    installed := by rw [heap]; exact origin.installed,
    outside := by rw [heap]; exact origin.outside,
    bounded := by
      intro ticket
      change (Stack.push (.armed data) stack).erase.ticketNames.count ticket ≤
        (CoreTicketHistory.capturedTickets (decision_result input).after.state.observations).count ticket
      rw [phase_decision_observations input]
      exact origin.bounded ticket }

omit evidence in
/-- At the actual current returned value, EmptyFocus discharges the mapping
prefix. Every normal-start runtime premise is derived from retained current
origin plus current returned control, not supplied as a future receipt. -/
def ArmedOrigin.runtime (origin : ArmedOrigin endpoint data stack)
    (returned : endpoint.state.control = .returned runtimeValue)
    (empty : EmptyFocus endpoint value runtimeScope) :
    CurrentArmedRuntime endpoint data stack runtimeValue := by
  have frames : endpoint.state.frames = endpoint.physical := by
    simpa only [empty.maps,framesOf,List.map_nil,List.nil_append] using endpoint.frames
  exact {
    cleanupOwners := origin.cleanupOwners, action := origin.action, environment := origin.environment,
    physical := origin.physical, returned := returned,
    frames := frames.trans origin.physicalSame,
    installed := origin.installed, outside := origin.outside, bounded := origin.bounded }

/-- The normal-start runtime bridge now consumes the current-produced armed
origin carrier, current value and empty-focus/control facts. It computes actual
Core entry and its original-root prefix; no current head is reconstructed from
CleanupRel alone and no desired successful successor is assumed. -/
theorem phase_normal_start_with_origin
    (site : PhaseSite globals outward world allowed actions phases budget ambient installations
      value runtimeScope (.push (.armed data) stack) result final context root)
    (current : PhaseCurrent program endpoint site)
    (related : CoreValueRelation.ValueRel graph endpoint.owners endpoint.state.heap runtimeValue value)
    (origin : ArmedOrigin endpoint data stack)
    (returned : endpoint.state.control = .returned runtimeValue)
    (empty : EmptyFocus endpoint value runtimeScope) :
    ∃ start : RunningStartPast graph origin.cleanupOwners origin.action origin.environment data
        runtimeValue value origin.physical stack,
      start.predecessor = endpoint.state ∧
      CoreMachine.next graph endpoint.state = .stepped (started start).state ∧
      CoreAllocationHistory.Steps graph (current.coreCount + 1)
        (CoreMachine.initial graph) (started start).state ∧
      (started start).state.nextCleanup = endpoint.state.nextCleanup :=
  phase_normal_start_runtime site current related (origin.runtime returned empty)


omit evidence in
private theorem phase_value_ordinary (closed : ClosedValue value) : LexicalUnwind.ordinary value := by
  have isValue := closed.1
  cases value <;> simp_all [LexicalUnwind.ordinary,Code.IsValue]

/-- Normal entry retains the whole current-produced callback authority,
including the full saved result Source/Auth and original Wait/root. Its actual
start and successor phase receipt share the SAME data/value/original suffix. -/
structure PhaseNormalStartEvent
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    {callbackDependencies : Dependencies} {callbackPlan : Plan callbackDependencies}
    {callbackRows : Rows (signature callbackPlan)}
    (site : PhaseSite globals outward world allowed actions phases budget ambient installations
      value runtimeScope (.push (.armed data) stack) result final
      (Context.cleanup (needs := requests) latent callbackRows context) root)
    (current : PhaseCurrent program endpoint site)
    (related : CoreValueRelation.ValueRel graph endpoint.owners endpoint.state.heap runtimeValue value)
    (origin : ArmedOrigin endpoint data stack) where
  authority : PhaseCallbackAuthority site related
  start : RunningStartPast graph origin.cleanupOwners origin.action origin.environment data
    runtimeValue value origin.physical stack
  predecessor : start.predecessor = endpoint.state
  after : PhaseCurrent program (started start) authority.next
  event : LexicalUnwind.Event current.run after.run
  issued : after.run.issued = current.run.issued
  completed : after.run.completed = current.run.completed
  count : after.eventCount = current.eventCount + 1
  actual : CoreMachine.next graph endpoint.state = .stepped (started start).state
  counter : (started start).state.nextCleanup = endpoint.state.nextCleanup
  positive : CoreUnwindRelation.Positive endpoint.point.machine (started start).point.machine [] []
  matching : Matching graph endpoint (started start) [] []
  ownership : CurrentOwnership graph origin.cleanupOwners (started start).state .none
    (.push (.running data value related.closed) stack)

/-- Connect full CURRENT armed value authority to its actual normal start.
Every successor Source/PhaseSite/private family/root and both causal histories
are outputs; no future endpoint identity, success or fresh key is a premise. -/
theorem phase_normal_start_event
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    {callbackDependencies : Dependencies} {callbackPlan : Plan callbackDependencies}
    {callbackRows : Rows (signature callbackPlan)}
    (site : PhaseSite globals outward world allowed actions phases budget ambient installations
      value runtimeScope (.push (.armed data) stack) result final
      (Context.cleanup (needs := requests) latent callbackRows context) root)
    (current : PhaseCurrent program endpoint site)
    (related : CoreValueRelation.ValueRel graph endpoint.owners endpoint.state.heap runtimeValue value)
    (origin : ArmedOrigin endpoint data stack)
    (returned : endpoint.state.control = .returned runtimeValue)
    (empty : EmptyFocus endpoint value runtimeScope) :
    Nonempty (PhaseNormalStartEvent site current related origin) := by
  obtain ⟨authority⟩ := phase_callback_authority site related
  obtain ⟨start,predecessor,actual,core,counter⟩ :=
    phase_normal_start_with_origin site current related origin returned empty
  have afterRelated : (started start).point.machine =
      .eval ⟨.app data.action .unit,.none,.push (.running data value related.closed) stack⟩ := rfl
  let run : LexicalUnwind.RunState :=
    ⟨(started start).point.machine,current.run.issued,current.run.completed⟩
  have transition : LexicalUnwind.Transition current.run.machine run.machine [] [] := by
    change LexicalUnwind.Transition current.run.machine (started start).point.machine [] []
    rw [current.machine,current.related,afterRelated]
    exact .evaluate (.startCleanup data value related.closed runtimeScope stack)
      (phase_value_ordinary related.closed)
  have fresh : (current.run.issued ++ []).Nodup := by
    simpa only [List.append_nil,LexicalUnwind.RunState.erase] using current.ledger.2
  have event : LexicalUnwind.Event current.run run := by
    simpa only [List.append_nil,List.nil_append] using LexicalUnwind.Event.step transition fresh
  have cleanupBound : ∀ identity, Owner.cleanup identity ∈ run.issued →
      identity < (started start).state.nextCleanup := by
    intro identity member
    rw [counter]
    exact current.cleanupBound identity member
  let after : PhaseCurrent program (started start) authority.next := {
    input := current.input, related := afterRelated,
    coreCount := current.coreCount + 1, core := core,
    run := run, machine := rfl, eventCount := current.eventCount + 1,
    past := .step current.past event, ledger := LexicalUnwind.event_preserves_ledger event current.ledger,
    cleanupBound := cleanupBound }
  have positive : CoreUnwindRelation.Positive endpoint.point.machine (started start).point.machine [] [] := by
    rw [current.related,afterRelated]
    exact .one (.evaluate (.startCleanup data value related.closed runtimeScope stack)
      (phase_value_ordinary related.closed))
  have ownership : CurrentOwnership graph origin.cleanupOwners (started start).state .none
      (.push (.running data value related.closed) stack) := by
    have owned := (normal_start_history origin.installed related origin.outside origin.bounded runtimeScope).2.1
    change CurrentOwnership graph origin.cleanupOwners
      (CoreGeneralRestoration.startedState start.predecessor origin.action origin.environment
        data.identity runtimeValue origin.physical) .none
      (.push (.running data value related.closed) stack)
    rw [predecessor]
    exact owned
  exact ⟨⟨authority,start,predecessor,after,event,rfl,rfl,rfl,actual,counter,positive,
    Matching.positive positive,ownership⟩⟩

/-- The actual callback-start event inherits whole lifetime ownership, including
absence of completed owners in its live normal callback stack. -/
theorem PhaseNormalStartEvent.endpoint_accounting
    (event : PhaseNormalStartEvent site current related origin) :
    Ledger event.after.run.erase ∧ event.after.run.completed.Nodup ∧
      (∀ owner, owner ∈ event.after.run.machine.stack.erase.owners → owner ∉ event.after.run.completed) :=
  event.after.past.ownership ⟨List.Perm.refl [],List.nodup_nil⟩


end
#check PhaseSite
#check PhaseSite.of_site
#check RegistrationBodyProjection.body_retained
#check RegistrationBodyProjection.normal_retained
#check RegistrationBodyProjection.body_phase
#check PhaseBetaPreserved
#check PhaseSite.beta
#check PhaseBranchPreserved
#check PhaseSite.branch
#check PhaseSavedValueAuthority
#check PhaseSite.saved_value
#print axioms RegistrationBodyProjection.body_retained
#print axioms RegistrationBodyProjection.normal_retained
#print axioms RegistrationBodyProjection.body_phase
#print axioms PhaseSite.beta
#print axioms PhaseSite.branch
#print axioms PhaseSite.saved_value

#check CleanupSourceParts
#check cleanup_source_parts
#check cleanup_authentication_parts
#check cleanup_code_parts
#check cleanup_resource_parts
#check cleanup_run_body
#check cleanup_wait_callback
#check registration_runtime
#check finish_runtime
#print axioms cleanup_source_parts
#print axioms cleanup_authentication_parts
#print axioms cleanup_code_parts
#print axioms cleanup_resource_parts
#print axioms cleanup_run_body
#print axioms cleanup_wait_callback
#print axioms registration_runtime
#print axioms finish_runtime
#check normal_registration_checks
#check normal_callback_finished_wait
#print axioms normal_registration_checks
#print axioms normal_callback_finished_wait
#check normal_saved_value
#check normal_callback_application
#print axioms normal_saved_value
#print axioms normal_callback_application
#check PhaseCurrent
#check PhaseCurrent.of_current
#check phase_initial
#check PhaseCurrent.cleanup_fresh
#check PhaseRegistrationEvent
#check phase_registration_event
#check PhaseRegistrationEvent.endpoint_accounting
#check PhaseBetaEvent
#check phase_beta_event
#print axioms PhaseCurrent.of_current
#print axioms phase_initial
#print axioms PhaseCurrent.cleanup_fresh
#print axioms phase_registration_event
#print axioms PhaseRegistrationEvent.endpoint_accounting
#print axioms phase_beta_event
#check phase_decision_nextCleanup
#check PhaseDecisionEvent
#check phase_decision_event
#print axioms phase_decision_nextCleanup
#print axioms phase_decision_event
#check phase_cleanup_retained_parts
#check PhaseCallbackAuthority
#check phase_callback_authority
#check CurrentArmedRuntime
#check phase_normal_start_runtime
#print axioms phase_cleanup_retained_parts
#print axioms phase_callback_authority
#print axioms phase_normal_start_runtime
#check ArmedOrigin
#check registration_armed_origin
#check ArmedOrigin.beta
#check phase_decision_observations
#check ArmedOrigin.decision
#check ArmedOrigin.runtime
#check phase_normal_start_with_origin
#print axioms registration_armed_origin
#print axioms ArmedOrigin.beta
#print axioms phase_decision_observations
#print axioms ArmedOrigin.decision
#print axioms ArmedOrigin.runtime
#print axioms phase_normal_start_with_origin
#check PhaseNormalStartEvent
#check phase_normal_start_event
#check PhaseNormalStartEvent.endpoint_accounting
#print axioms phase_normal_start_event
#print axioms PhaseNormalStartEvent.endpoint_accounting
end Ash.OneShot.CoreCallableRichNormalCleanupPhases
