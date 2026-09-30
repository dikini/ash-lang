import CoreCallableContractAdmission

/-! Finite effect-boundary gate for the indexed experimental judgment. All
functions and requests share one global exact operation contract. This does
not supply handler/capture/pending or full M4 admission. -/
namespace Ash.OneShot.CoreCallableContractAdmissionExamples
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractSource (Contract Environment sequenceRows)
open CoreCallableContractAdmission
open SourcePlannedChecks (Certified DeclarationPolicy)
open RecursiveRequirements (Requirements)
open CoreCallableRootRefinement (Refines)

private def effect : Instance := .user 9 []
private def request : Demand := ⟨effect, 0, false⟩
private def emptyReq : Requirements [] := .request [] []
private def operationReq : Requirements [] := .emitAfter emptyReq [] [request]
private def operationPlan : Plan (.sequence .pure (.request effect 0)) := .sequence .pure .request
private def operationRows : Rows (signature operationPlan) := sequenceRows Rows.pure Rows.request
private def action : Contract := .function .unit .unit [effect] [request] operationPlan operationRows
private def globals : Globals where
  operations := fun e operation => if e = effect ∧ operation = 0 then some (.unit, .unit) else none
  policy := fun _ => ⟨false, false⟩
  owners := fun _ => none
private def run : Code := .perform (Instantiation.freezeEffect effect) 0 .unit
private def simple : Code := .lambda 2 run
private def sequenced : Code := .lambda 2 (.bind 3 .unit run)

section
variable [DeclarationPolicy]

private theorem planCertified : Certified outward world operationPlan := .sequence .pure .request
omit [DeclarationPolicy] in
private theorem actionFormed : ScopedPorts.InWorld world action.port := by
  change [] ⊆ world
  intro identity member; cases member

private theorem run_source : Source globals outward world [effect] scope environment run .unit [] operationReq operationPlan operationRows :=
  .perform (by simp [globals, Globals.registry]) (by simp) .unit (by change [] ⊆ world; intro identity member; cases member)

omit [DeclarationPolicy] in
private theorem operation_outward : RecursiveOutward.Outward operationReq (some [request]) := by
  exact .emitAfter (layers := []) (.request (layers := []))

private theorem simple_source : Source globals outward world allowed scope environment simple action [] emptyReq .pure Rows.pure :=
  .lambda run_source (Refines.identity operationRows) operation_outward (by simp [request]) planCertified actionFormed

private theorem sequenced_source : Source globals outward world allowed scope environment sequenced action [] emptyReq .pure Rows.pure := by
  refine .lambda (.bind .unit run_source) ?_ ?_ (by simp [request]) planCertified actionFormed
  · exact Refines.of_exact (CoreCallableRefinementTransport.Refines.pure_prefix CorePayloadRefinement.PurePlan.pure Rows.pure operationRows)
  · exact .sequence (.request (layers := [])) operation_outward

private def helperBody : Code := .app (.variable 0) .unit
private def helper : Code := .lambda 0 helperBody
private def helperPlan := Plan.sequence Plan.pure (Plan.sequence Plan.pure operationPlan)
private def helperRows : Rows (signature helperPlan) := sequenceRows Rows.pure (sequenceRows Rows.pure operationRows)
private def helperReq : Requirements [] := .emitAfter (.sequence emptyReq emptyReq) [] [request]
private def helperContract : Contract := .function action .unit [effect] [request] helperPlan helperRows
private theorem helperCertified : Certified outward world helperPlan := .sequence .pure (.sequence .pure planCertified)
private theorem helper_source : Source globals outward world allowed scope environment helper helperContract [] emptyReq .pure Rows.pure := by
  refine .lambda (.app (.variable (by simp [Environment.extend, action]) actionFormed) .unit (by simp) planCertified)
    (Refines.identity helperRows) ?_ (by simp [request]) helperCertified ?_
  · exact .emitAfter (layers := []) (.sequence (.request (layers := [])) (.request (layers := [])))
  · simp [Contract.port, Contract.value, SourcePlannedTyping.Value.erase,
      SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port, ScopedPorts.InWorld,
      ScopedPorts.Port.resources, List.flatMap, Instance.resources, effect,
      action]

private def callPlan := Plan.sequence Plan.pure (Plan.sequence Plan.pure helperPlan)
private def callRows : Rows (signature callPlan) := sequenceRows Rows.pure (sequenceRows Rows.pure helperRows)
private def callReq : Requirements [] := .emitAfter (.sequence emptyReq emptyReq) [] [request]
private def bothBody : Code := .bind 11 (.app (.variable 10) simple) (.app (.variable 10) sequenced)
private def both : Code := .bind 10 helper bothBody

/-- One helper is bound once and consumes two unchanged effectful closures
under the same public callable contract and exact global registry. -/
theorem both_source : Source globals outward world [effect] scope Environment.empty both .unit []
    (.sequence emptyReq (.sequence callReq callReq))
    (.sequence .pure (.sequence callPlan callPlan))
    (sequenceRows Rows.pure (sequenceRows callRows callRows)) := by
  have formed : ScopedPorts.InWorld world helperContract.port := by
    change [] ⊆ world
    intro identity member; cases member
  apply Source.bind helper_source
  unfold bothBody
  apply Source.bind (initialDemand := []) (bodyDemand := [])
  · exact .app (input := action) (output := Contract.unit) (requests := [effect]) (latent := [request])
      (.variable (by simp [Environment.extend, helperContract]) formed) simple_source (by simp) helperCertified
  · exact .app (input := action) (output := Contract.unit) (requests := [effect]) (latent := [request])
      (.variable (by simp [Environment.extend, helperContract]) formed) sequenced_source (by simp) helperCertified

omit [DeclarationPolicy] in
/-- Actual operation argument/result contracts are read from that same table. -/
theorem exact_operation : globals.operations effect 0 = some (Contract.unit, Contract.unit) := by simp [globals]

/-- The fixed registry cannot be reselected by a request constructor. -/
theorem wrong_result_rejected : ¬ Source globals outward world [effect] scope environment run .boolean demand requirements plan rows := by
  intro source
  obtain ⟨input, known⟩ := (IndexedSource.request_contract source)
  simp [globals, Globals.registry] at known

/-- The same exact key cannot accept an integer where Unit is declared. -/
theorem wrong_input_rejected :
    ¬ Source globals outward world [effect] scope environment
      (.perform (Instantiation.freezeEffect effect) 0 (.integer 7)) .unit demand requirements plan rows := by
  intro source
  obtain ⟨input, operandDemand, operandReq, operandDeps, operandPlan, operandRows, known, operand⟩ := (IndexedSource.request_operand source)
  simp [globals, Globals.registry] at known
  subst input
  cases operand

/-- An absent operation key has no fabricated signature fallback. -/
theorem wrong_key_rejected :
    ¬ Source globals outward world [effect] scope environment
      (.perform (Instantiation.freezeEffect effect) 1 .unit) output demand requirements plan rows := by
  intro source
  obtain ⟨input, known⟩ := (IndexedSource.request_contract source)
  simp [globals, Globals.registry] at known

/-- Closed substitution retains recursive private plans and their actual
certification for both payloads, not just their ordinary ports. -/
theorem helper_substitutions :
    Source globals outward world [effect] .none Environment.empty (.app simple .unit) .unit [] helperReq helperPlan helperRows ∧
    Source globals outward world [effect] .none Environment.empty (.app sequenced .unit) .unit [] helperReq helperPlan helperRows ∧
    Certified outward world helperPlan := by
  have body : Source globals outward world [effect] .none (Environment.empty.extend 0 action) helperBody .unit [] helperReq helperPlan helperRows :=
    .app (.variable (by simp [Environment.extend, action]) actionFormed) .unit (by simp) planCertified
  have simpleClosed : ClosedValue simple := by
    simp [simple, run, effect, ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames, Code.dependencies, Instantiation.freezeEffect, Instantiation.Effect.freeNames]
  have sequencedClosed : ClosedValue sequenced := by
    simp [sequenced, run, effect, ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames, Code.dependencies, Syntax.without, Instantiation.freezeEffect, Instantiation.Effect.freeNames]
  exact ⟨by simpa [helperBody, Code.subst] using (IndexedSource.closed_substitution body) simple_source simpleClosed,
    by simpa [helperBody, Code.subst] using (IndexedSource.closed_substitution body) sequenced_source sequencedClosed, (IndexedSource.certified body)⟩


omit [DeclarationPolicy] in
private theorem helper_closed : ClosedValue helper := by
  simp [helper, helperBody, ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames,
    Code.dependencies, Syntax.without]
omit [DeclarationPolicy] in
private theorem simple_closed : ClosedValue simple := by
  simp [simple, run, effect, ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames,
    Code.dependencies, Instantiation.freezeEffect, Instantiation.Effect.freeNames]
omit [DeclarationPolicy] in
private theorem sequenced_closed : ClosedValue sequenced := by
  simp [sequenced, run, effect, ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames,
    Code.dependencies, Syntax.without, Instantiation.freezeEffect, Instantiation.Effect.freeNames]

/-- The first actual bind preserves private witnesses from both_source. -/
theorem both_bind (stack : Stack) :
    Source globals outward world [effect] scope Environment.empty (bothBody.subst 10 helper) .unit []
      (.sequence callReq callReq) (.sequence callPlan callPlan) (sequenceRows callRows callRows) ∧
    Certified outward world (.sequence callPlan callPlan) ∧
    RawStep ⟨both, scope, stack⟩ ⟨bothBody.subst 10 helper, scope, stack⟩ [] [] :=
  (IndexedSource.bind_step both_source) helper_closed (by
    simp [bothBody, simple, sequenced, run, effect, ClosedExcept, Code.dependencies, Syntax.without,
      Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources]) stack

private def retaining (identity : Nat) : Code := .lambda 2 (.bind 3 (.resourceRef (.activation identity)) run)
private theorem retaining_source (issued : identity ∈ world) :
    Source globals outward world allowed scope environment (retaining identity) action [] emptyReq .pure Rows.pure := by
  refine .lambda (.bind (.reference issued) run_source) ?_ ?_ (by simp [request]) planCertified actionFormed
  · exact Refines.of_exact (CoreCallableRefinementTransport.Refines.pure_prefix CorePayloadRefinement.PurePlan.pure Rows.pure operationRows)
  · exact .sequence (.request (layers := [])) operation_outward

/-- Exact request ports remain resource-free, but actual retained support does not. -/
theorem retaining_supported (issued : identity ∈ world) :
    CoreCallableContractAdmission.Supported globals outward world [effect] scope Environment.empty (fun _ => []) (retaining identity) action [] emptyReq .pure Rows.pure [identity] := by
  apply CoreCallableContractAdmission.Supported.canonical (retaining_source issued)
  simpa [retaining, run, effect, ScopedPorts.Support.evaluate, Code.dependencies,
    Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources, Syntax.without] using (show [identity] ⊆ world from by simpa using issued)

/-- A resource-free port cannot justify a false empty actual capture bound. -/
theorem wrong_support_rejected :
    ¬ CoreCallableContractAdmission.Supported globals outward world [effect] scope Environment.empty (fun _ => []) (retaining identity) action [] emptyReq .pure Rows.pure [] := by
  intro supported
  have member := supported.support.resources (show identity ∈ Syntax.resourceDependencies (retaining identity).dependencies from by
    simp [retaining, run, effect, Syntax.resourceDependencies, Code.dependencies, Syntax.without,
      Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources])
  cases member

private def payload (extra : Bool) : Code := if extra then sequenced else simple
private theorem payload_source : Source globals outward world [effect] scope Environment.empty (payload extra) action [] emptyReq .pure Rows.pure := by
  cases extra <;> first | exact simple_source | exact sequenced_source
omit [DeclarationPolicy] in
private theorem payload_closed : ClosedValue (payload extra) := by
  cases extra <;> first | exact simple_closed | exact sequenced_closed

/-- Actual helper beta uses that same supplied global-indexed payload derivation,
recovering and certifying the private body through compositional substitution. -/
theorem helper_beta (extra : Bool) (stack : Stack) :
    ∃ (bodyDemand : List Nat) (bodyReq : Requirements bodyDemand) (actualDependencies : SourceDependencyAnnotations.Dependencies)
      (actualPlan : Plan actualDependencies) (actualRows : Rows (signature actualPlan)),
      Source globals outward world [effect] .none Environment.empty (helperBody.subst 0 (payload extra)) .unit bodyDemand bodyReq actualPlan actualRows ∧
      Certified outward world actualPlan ∧ Refines helperRows actualRows ∧ RecursiveOutward.Outward bodyReq (some [request]) ∧
      RawStep ⟨.app helper (payload extra), scope, stack⟩ ⟨helperBody.subst 0 (payload extra), .none, stack⟩ [] [] :=
  IndexedSource.beta (helper_source (allowed := [effect])) payload_source payload_closed helper_closed stack

/-- Effect-boundary beta has actual source/certification and transports exact
current certificates plus checked roots. No successor admission is a premise. -/
theorem helper_current (extra : Bool) (stack : Stack)
    (installations ambient : List Nat) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases) (budget : Footprint)
    {receivingScope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints receivingScope}
    (context : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Context hints)
    (certificate : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.SourceAdmission.Code outward actions budget phases world installations helperRows context)
    (certificateChecked : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.CodeChecked ambient outward certificate)
    (root annotated : Requirements demand)
    (run : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.Run world installations helperRows context root)
    (entries : RecursiveRequirements.Store) (receiving : OwnerPhases.Context) (row : Footprint)
    (annotation : SourceDependencyAnnotations.RowAnnotation root annotated)
    (check : RecursiveRequirements.Checked entries receiving phases (SourceScheduledCleanupInterfaces.Lexical.Recursive.annotateDisposals annotated) row)
    (bounded : row ⊆ budget) :
    ∃ (actualDependencies : SourceDependencyAnnotations.Dependencies) (actualPlan : Plan actualDependencies)
      (actualRows : Rows (signature actualPlan)), ∃ (bodyDemand : List Nat) (bodyReq : Requirements bodyDemand),
      Source globals outward world [effect] .none Environment.empty (helperBody.subst 0 (payload extra)) .unit bodyDemand bodyReq actualPlan actualRows ∧
      Certified outward world actualPlan ∧
      RawStep ⟨.app helper (payload extra), scope, stack⟩ ⟨helperBody.subst 0 (payload extra), .none, stack⟩ [] [] ∧
      ∃ actualCertificate : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.SourceAdmission.Code outward actions budget phases world installations actualRows context,
        SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.CodeChecked ambient outward actualCertificate ∧
        ∃ actualRoot actualAnnotated : Requirements demand, ∃ actualRow : Footprint,
          SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.Run world installations actualRows context actualRoot ∧
          CoreCallableRootRefinement.RootTransport root actualRoot ∧ SourceDependencyAnnotations.RowAnnotation actualRoot actualAnnotated ∧
          RecursiveRequirements.Checked entries receiving phases (SourceScheduledCleanupInterfaces.Lexical.Recursive.annotateDisposals actualAnnotated) actualRow ∧ actualRow ⊆ budget :=
  IndexedSource.beta_current (helper_source (allowed := [effect])) payload_source payload_closed helper_closed stack installations ambient actions phases budget
    context certificate certificateChecked root annotated run entries receiving row annotation check bounded

private def payloadBody (extra : Bool) : Code := if extra then .bind 3 .unit run else run
/-- Invoke the selected effectful payload itself. Current checking transports
into its recovered private operation body (including the extra sequence). -/
theorem payload_current (extra : Bool) (stack : Stack)
    (installations ambient : List Nat) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases) (budget : Footprint)
    {receivingScope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints receivingScope}
    (context : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Context hints)
    (certificate : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.SourceAdmission.Code outward actions budget phases world installations operationRows context)
    (certificateChecked : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.CodeChecked ambient outward certificate)
    (root annotated : Requirements demand)
    (run : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.Run world installations operationRows context root)
    (entries : RecursiveRequirements.Store) (receiving : OwnerPhases.Context) (row : Footprint)
    (annotation : SourceDependencyAnnotations.RowAnnotation root annotated)
    (check : RecursiveRequirements.Checked entries receiving phases (SourceScheduledCleanupInterfaces.Lexical.Recursive.annotateDisposals annotated) row)
    (bounded : row ⊆ budget) :
    ∃ (actualDependencies : SourceDependencyAnnotations.Dependencies) (actualPlan : Plan actualDependencies)
      (actualRows : Rows (signature actualPlan)), ∃ (bodyDemand : List Nat) (bodyReq : Requirements bodyDemand),
      Source globals outward world [effect] .none Environment.empty ((payloadBody extra).subst 2 .unit) .unit bodyDemand bodyReq actualPlan actualRows ∧
      Certified outward world actualPlan ∧
      RawStep ⟨.app (payload extra) .unit, scope, stack⟩ ⟨(payloadBody extra).subst 2 .unit, .none, stack⟩ [] [] ∧
      ∃ actualCertificate : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.SourceAdmission.Code outward actions budget phases world installations actualRows context,
        SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.CodeChecked ambient outward actualCertificate ∧
        ∃ actualRoot actualAnnotated : Requirements demand, ∃ actualRow : Footprint,
          SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.Run world installations actualRows context actualRoot ∧
          CoreCallableRootRefinement.RootTransport root actualRoot ∧ SourceDependencyAnnotations.RowAnnotation actualRoot actualAnnotated ∧
          RecursiveRequirements.Checked entries receiving phases (SourceScheduledCleanupInterfaces.Lexical.Recursive.annotateDisposals actualAnnotated) actualRow ∧ actualRow ⊆ budget := by
  cases extra
  · exact IndexedSource.beta_current (simple_source (allowed := [effect])) Source.unit ScopedExecution.Examples.unit_closed simple_closed stack
      installations ambient actions phases budget context certificate certificateChecked root annotated run entries receiving row annotation check bounded
  · exact IndexedSource.beta_current (sequenced_source (allowed := [effect])) Source.unit ScopedExecution.Examples.unit_closed sequenced_closed stack
      installations ambient actions phases budget context certificate certificateChecked root annotated run entries receiving row annotation check bounded

#print axioms payload_current
#print axioms wrong_input_rejected
#print axioms wrong_key_rejected
#print axioms both_bind
#print axioms retaining_supported
#print axioms wrong_support_rejected
#print axioms helper_beta
#print axioms helper_current
#print axioms both_source
#print axioms exact_operation
#print axioms wrong_result_rejected
#print axioms helper_substitutions
end
end Ash.OneShot.CoreCallableContractAdmissionExamples
