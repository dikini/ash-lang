import CoreCallableContractSource

/-! Whole-expression gates for the separate DN-0033 contract-source judgment.
The unchanged lambda bodies share a public checking contract, not their private
plans. These examples do not construct legacy Auth or whole M4 admission. -/
namespace Ash.OneShot.CoreCallableContractExamples
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractSource
open CoreCallableRootRefinement (Refines RootTransport)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open RecursiveRequirements (Requirements Checked)
open SourceDependencyAnnotations (RowAnnotation)
open SourceScheduledCleanupInterfaces.Lexical.Recursive (annotateDisposals)

/-- The one declared Unit → Unit port and pure checking contract. -/
def action : Contract := .function .unit .unit [] [] .pure Rows.pure
def simple : Code := .lambda 2 .unit
def sequenced : Code := .lambda 2 (.bind 3 .unit .unit)
def retaining (identity : Nat) : Code := .lambda 2 (.bind 3 (.resourceRef (.activation identity)) .unit)
def pairPlan := Plan.sequence Plan.pure Plan.pure
def pairRows : Rows (signature pairPlan) := sequenceRows Rows.pure Rows.pure

theorem pureRefinement {plan : Plan dependencies} (structural : CorePayloadRefinement.PurePlan plan)
    (rows : Rows (signature plan)) : Refines Rows.pure rows :=
  Refines.of_exact (CoreCallableRefinementTransport.Refines.pure_plan structural rows)

variable {world : List Nat} {allowed : List Instance} {environment : Environment}

theorem simple_source : Source world allowed environment simple action .pure Rows.pure :=
  .lambda .unit (Refines.identity Rows.pure) (by intro identity member; cases member)

theorem sequenced_source : Source world allowed environment sequenced action .pure Rows.pure :=
  .lambda (.bind .unit .unit) (pureRefinement (.sequence .pure .pure) pairRows)
    (by intro identity member; cases member)

theorem retaining_source (identity : Nat) (issued : identity ∈ world) :
    Source world allowed environment (retaining identity) action .pure Rows.pure :=
  .lambda (.bind (.reference issued) .unit) (pureRefinement (.sequence .pure .pure) pairRows)
    (by intro identity member; cases member)

def applyBody : Code := .app (.variable 0) .unit
def applyHelper : Code := .lambda 0 applyBody
def callPlan := Plan.sequence Plan.pure (Plan.sequence Plan.pure Plan.pure)
def callRows : Rows (signature callPlan) := sequenceRows Rows.pure (sequenceRows Rows.pure Rows.pure)
def helper : Contract := .function action .unit [] [] .pure Rows.pure

theorem helper_source : Source world allowed environment applyHelper helper .pure Rows.pure := by
  apply Source.lambda (actualRows := callRows)
  · exact .app (.variable (contract := action) (by simp [Environment.extend]) (by intro identity member; cases member)) .unit (List.nil_subset _)
  · exact pureRefinement (.sequence .pure (.sequence .pure .pure)) callRows
  · intro identity member; cases member

/-- Bind the helper once, then use it with both unchanged closure bodies under
one common parameter contract. The derivation is for the whole expression. -/
def bothBody : Code := .bind 11 (.app (.variable 10) simple) (.app (.variable 10) sequenced)
def both : Code := .bind 10 applyHelper bothBody
def bothPlan := Plan.sequence Plan.pure (Plan.sequence callPlan callPlan)
def bothRows : Rows (signature bothPlan) := sequenceRows Rows.pure (sequenceRows callRows callRows)

theorem both_source : Source world allowed environment both .unit bothPlan bothRows := by
  apply Source.bind helper_source
  apply Source.bind
  · exact .app (.variable (contract := helper) (by simp [Environment.extend]) (by intro identity member; cases member)) simple_source (List.nil_subset _)
  · exact .app (.variable (contract := helper) (by simp [Environment.extend]) (by intro identity member; cases member)) sequenced_source (List.nil_subset _)

/-- The whole helper expression also accepts the independently supported
retaining payload through precisely the same action contract. -/
def retainedBody (identity : Nat) : Code := .app (.variable 10) (retaining identity)
def retained (identity : Nat) : Code := .bind 10 applyHelper (retainedBody identity)
def retainedPlan := Plan.sequence Plan.pure callPlan
def retainedRows : Rows (signature retainedPlan) := sequenceRows Rows.pure callRows

theorem retained_source (identity : Nat) (issued : identity ∈ world) :
    Source world allowed environment (retained identity) .unit retainedPlan retainedRows :=
  .bind helper_source (.app (.variable (contract := helper) (by simp [Environment.extend]) (by intro key member; cases member))
    (retaining_source identity issued) (List.nil_subset _))

/-- A branch has one common callable result while preserving both actual
lambda-body derivations. The caller then applies that selected callable. -/
def choose (choice : Bool) : Code := .branch (.boolean choice) simple sequenced
def choosePlan := Plan.sequence Plan.pure (Plan.choice Plan.pure Plan.pure)
def chooseRows : Rows (signature choosePlan) := sequenceRows Rows.pure (choiceRows Rows.pure Rows.pure)
theorem choose_source (choice : Bool) : Source world allowed environment (choose choice) action choosePlan chooseRows :=
  .branch .boolean simple_source sequenced_source

def chosenCall (choice : Bool) : Code := .bind 12 (choose choice) (.app (.variable 12) .unit)
def chosenCallPlan := Plan.sequence choosePlan callPlan
def chosenCallRows : Rows (signature chosenCallPlan) := sequenceRows chooseRows callRows

theorem chosenCall_source (choice : Bool) :
    Source world allowed environment (chosenCall choice) .unit chosenCallPlan chosenCallRows :=
  .bind (choose_source choice)
    (.app (.variable (contract := action) (by simp [Environment.extend]) (by intro identity member; cases member)) .unit (List.nil_subset _))

/-- A function returns either callable under the common result contract; the
caller uses that result. This transports a higher-order result through bind. -/
def returning (choice : Bool) : Code := .lambda 4 (choose choice)
def producer : Contract := .function .unit action [] [] .pure Rows.pure
theorem returning_source (choice : Bool) :
    Source world allowed environment (returning choice) producer .pure Rows.pure :=
  .lambda (choose_source choice)
    ((Refines.identity Rows.pure).choice (Refines.identity Rows.pure) |>.compose
      (Refines.of_exact (CoreCallableRefinementTransport.Refines.pure_prefix CorePayloadRefinement.PurePlan.pure Rows.pure
        (choiceRows (first := Plan.pure) (second := Plan.pure) Rows.pure Rows.pure))))
    (by intro identity member; cases member)

def returnedCall (choice : Bool) : Code := .bind 12 (.app (returning choice) .unit) (.app (.variable 12) .unit)
def returnedCallPlan := Plan.sequence callPlan callPlan
def returnedCallRows : Rows (signature returnedCallPlan) := sequenceRows callRows callRows
theorem returnedCall_source (choice : Bool) :
    Source world allowed environment (returnedCall choice) .unit returnedCallPlan returnedCallRows :=
  .bind (.app (returning_source choice) .unit (List.nil_subset _))
    (.app (.variable (contract := action) (by simp [Environment.extend]) (by intro identity member; cases member)) .unit (List.nil_subset _))

theorem helper_closed : ClosedValue applyHelper := by
  simp [applyHelper, applyBody, ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames,
    Code.dependencies, Syntax.without]
theorem simple_closed : ClosedValue simple := by
  simp [simple, ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames, Code.dependencies]
theorem sequenced_closed : ClosedValue sequenced := by
  simp [sequenced, ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames, Code.dependencies, Syntax.without]
theorem retaining_closed (identity : Nat) : ClosedValue (retaining identity) := by
  simp [retaining, ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames,
    Instantiation.ResourceName.freeNames, Code.dependencies, Syntax.without]

/-- This step and its successor source are derived from the whole bind-once
source, rather than a separate specialization of a legacy rich type. -/
theorem both_bind (runtimeScope : Execution.Scope) (stack : Stack) :
    Source world allowed environment (bothBody.subst 10 applyHelper) .unit
      (.sequence callPlan callPlan) (sequenceRows callRows callRows) ∧
      RawStep ⟨both, runtimeScope, stack⟩ ⟨bothBody.subst 10 applyHelper, runtimeScope, stack⟩ [] [] := by
  apply (both_source (world := world) (allowed := allowed) (environment := environment)).bind_step helper_closed
  intro name member
  simpa [bothBody, simple, sequenced, Code.dependencies, Syntax.without] using member

/-- Recover certification from the actual recursive private helper-body source.
Contract refinement alone was not used as a certification proof. -/
theorem helper_body_certified [SourcePlannedChecks.DeclarationPolicy]
    (source : Source world [] (environment.extend 0 action) applyBody .unit actualPlan actualRows) :
    SourcePlannedChecks.Certified outward world actualPlan := by
  cases source with
  | app function argument admitted =>
    cases function with
    | «variable» known formed =>
      have same := Option.some.inj (by simpa [Environment.extend] using known)
      cases same
      cases argument
      exact .sequence .pure (.sequence .pure .pure)

theorem simple_body_certified [SourcePlannedChecks.DeclarationPolicy]
    (source : Source world allowed environment .unit .unit actualPlan actualRows) :
    SourcePlannedChecks.Certified outward world actualPlan := by cases source; exact .pure

theorem sequenced_body_certified [SourcePlannedChecks.DeclarationPolicy]
    (source : Source world allowed environment (.bind 3 .unit .unit) .unit actualPlan actualRows) :
    SourcePlannedChecks.Certified outward world actualPlan := by
  cases source with
  | bind initial body => cases initial; cases body; exact .sequence .pure .pure

theorem retaining_body_certified [SourcePlannedChecks.DeclarationPolicy]
    (source : Source world allowed environment (.bind 3 (.resourceRef (.activation identity)) .unit) .unit actualPlan actualRows) :
    SourcePlannedChecks.Certified outward world actualPlan := by
  cases source with
  | bind initial body => cases initial; cases body; exact .sequence .pure .pure

/-- The same helper's private body is recovered at either argument. Substitution
keeps its actual checking plan, and its certification is derived from that body.
The generic beta_current theorem supplies Code/CodeChecked/root transport for
these very helper and argument source derivations. -/
theorem helper_invocation [SourcePlannedChecks.DeclarationPolicy]
    (argument : Source world [] environment value action argumentPlan argumentRows)
    (closed : ClosedValue value) (runtimeScope : Execution.Scope) (stack : Stack) :
    ∃ (dependencies : SourceDependencyAnnotations.Dependencies) (actualPlan : Plan dependencies)
      (actualRows : Rows (signature actualPlan)),
      Source world [] environment (applyBody.subst 0 value) .unit actualPlan actualRows ∧
      SourcePlannedChecks.Certified outward world actualPlan ∧ Refines Rows.pure actualRows ∧
      RawStep ⟨.app applyHelper value, runtimeScope, stack⟩
        ⟨applyBody.subst 0 value, .none, stack⟩ [] [] := by
  obtain ⟨dependencies, plan, rows, bodySource, refinement⟩ :=
    (helper_source (world := world) (allowed := []) (environment := environment)).lambda_body
  exact ⟨dependencies, plan, rows, bodySource.closed_substitution argument closed,
    helper_body_certified bodySource, refinement,
    .beta 0 applyBody value runtimeScope stack closed helper_closed⟩

/-- A true/false reduction selects a callable derivation from the same branch
source. Applying that result then recovers its private actual body by beta. -/
theorem true_choice (runtimeScope : Execution.Scope) (stack : Stack) :
    Source world allowed environment simple action .pure Rows.pure ∧
      RawStep ⟨choose true, runtimeScope, stack⟩ ⟨simple, runtimeScope, stack⟩ [] [] :=
  (choose_source true).true_step runtimeScope stack

theorem false_choice (runtimeScope : Execution.Scope) (stack : Stack) :
    Source world allowed environment sequenced action .pure Rows.pure ∧
      RawStep ⟨choose false, runtimeScope, stack⟩ ⟨sequenced, runtimeScope, stack⟩ [] [] :=
  (choose_source false).false_step runtimeScope stack

/-- Computed support of the closed retaining lambda, independent of its empty
request port. Empty lexical support is appropriate here because no ordinary
free variable remains; the actual literal cell dependency is retained. -/
theorem retaining_supported (identity : Nat) (issued : identity ∈ world) :
    CoreCallableContractSource.Supported world allowed environment ScopedPorts.Support.empty (retaining identity) action .pure Rows.pure [identity] := by
  apply Supported.canonical (retaining_source identity issued)
  simpa [retaining, Code.dependencies, Syntax.without, ScopedPorts.Support.evaluate, List.cons_subset] using
    issued

/-- The branch can also select a retaining arm at the unchanged declared port. -/
def chooseRetaining (choice : Bool) (identity : Nat) : Code := .branch (.boolean choice) simple (retaining identity)
theorem chooseRetaining_source (choice : Bool) (identity : Nat) (issued : identity ∈ world) :
    Source world allowed environment (chooseRetaining choice identity) action choosePlan chooseRows :=
  .branch .boolean simple_source (retaining_source identity issued)

theorem chooseRetaining_supported (choice : Bool) (identity : Nat) (issued : identity ∈ world) :
    CoreCallableContractSource.Supported world allowed environment ScopedPorts.Support.empty (chooseRetaining choice identity) action choosePlan chooseRows [identity] := by
  apply Supported.canonical (chooseRetaining_source choice identity issued)
  simpa [chooseRetaining, simple, retaining, Code.dependencies, Syntax.without, ScopedPorts.Support.evaluate, List.cons_subset] using
    issued

theorem false_retaining_choice (identity : Nat) (issued : identity ∈ world)
    (runtimeScope : Execution.Scope) (stack : Stack) :
    Source world allowed environment (retaining identity) action .pure Rows.pure ∧
      RawStep ⟨chooseRetaining false identity, runtimeScope, stack⟩ ⟨retaining identity, runtimeScope, stack⟩ [] [] :=
  (chooseRetaining_source false identity issued).false_step runtimeScope stack

/-- Actual body certification, support and current contextual checking are
obtained together at the helper beta. The private body source is recovered from
the helper lambda that appears in both_source and retained_source. -/
theorem helper_current [SourcePlannedChecks.DeclarationPolicy]
    (argument : Source world [] environment value action argumentPlan argumentRows)
    (closed : ClosedValue value)
    (valueIssued : Syntax.resourceDependencies value.dependencies ⊆ world)
    (runtimeScope : Execution.Scope) (stack : Stack)
    (installations ambient : List Nat) (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases) (budget : Footprint)
    {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope}
    (context : Context hints)
    (certificate : SourceAdmission.Code outward actions budget phases world installations Rows.pure context)
    (certificateChecked : InstallationSupport.CodeChecked ambient outward certificate)
    (root annotated : Requirements demand)
    (run : Accounting.Run world installations Rows.pure context root)
    (entries : RecursiveRequirements.Store) (receiving : OwnerPhases.Context) (row : Footprint)
    (annotation : RowAnnotation root annotated)
    (check : Checked entries receiving phases (annotateDisposals annotated) row) (bounded : row ⊆ budget) :
    ∃ (dependencies : SourceDependencyAnnotations.Dependencies) (actualPlan : Plan dependencies)
      (actualRows : Rows (signature actualPlan)),
      CoreCallableContractSource.Supported world [] environment ScopedPorts.Support.empty
        (applyBody.subst 0 value) .unit actualPlan actualRows (Syntax.resourceDependencies value.dependencies) ∧
      SourcePlannedChecks.Certified outward world actualPlan ∧
      RawStep ⟨.app applyHelper value, runtimeScope, stack⟩ ⟨applyBody.subst 0 value, .none, stack⟩ [] [] ∧
      ∃ actualCertificate : SourceAdmission.Code outward actions budget phases world installations actualRows context,
        InstallationSupport.CodeChecked ambient outward actualCertificate ∧
        ∃ actualRoot actualAnnotated : Requirements demand, ∃ actualRow : Footprint,
          Accounting.Run world installations actualRows context actualRoot ∧ RootTransport root actualRoot ∧
          RowAnnotation actualRoot actualAnnotated ∧
          Checked entries receiving phases (annotateDisposals actualAnnotated) actualRow ∧ actualRow ⊆ budget := by
  obtain ⟨dependencies, plan, rows, bodySource, refinement⟩ :=
    (helper_source (world := world) (allowed := []) (environment := environment)).lambda_body
  have afterSource := bodySource.closed_substitution argument closed
  have support : CoreCallableContractSource.Supported world [] environment ScopedPorts.Support.empty
      (applyBody.subst 0 value) .unit plan rows (Syntax.resourceDependencies value.dependencies) := by
    refine ⟨afterSource, ?_, valueIssued⟩
    apply SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mpr
    simp [applyBody, Code.subst, Code.dependencies, ScopedPorts.Support.empty_evaluation]
  let actualCertificate := refinement.code outward actions budget phases world installations context certificate
  obtain ⟨actualRoot, actualAnnotated, actualRow, actualRun, transport, actualAnnotation, actualCheck, actualBound⟩ :=
    CoreCallableRootRefinement.checked_accounting refinement world installations context root annotated run
      entries receiving phases budget row annotation check bounded
  exact ⟨dependencies, plan, rows, support, helper_body_certified bodySource,
    .beta 0 applyBody value runtimeScope stack closed helper_closed,
    actualCertificate, refinement.checked ambient outward actions budget phases world installations context certificate certificateChecked,
    actualRoot, actualAnnotated, actualRow, actualRun, transport, actualAnnotation, actualCheck, actualBound⟩

/-- Receiving resources are selected from an actual handler/cell cut, using the
computed dependency support of the contract-source payload. -/
def receiverAccepts (code : Code) (scope : SourceDependencyCapture.Scope) (ambient : List Nat) : Prop :=
  match SourceDependencyCapture.select CorePayloadRefinement.invoke 0 scope with
  | some (.handler _ receiving _ _) => Syntax.resourceDependencies code.dependencies ⊆ receiving.visibleResources ++ ambient
  | _ => False

section Receivers
variable {operations : SourcePlannedTyping.Operations} {policy : Syntax.TicketPolicy}
  {contracts : SourcePlannedTyping.Contracts} {ports : OperationRows operations} {owners : ContractRows contracts}

theorem actual_receivers (identity : Nat) (issued : identity ∈ world) :
    let payload := CorePayloadRefinement.retaining (operations := operations) (policy := policy)
      (contracts := contracts) (ports := ports) (owners := owners) identity issued
    SourceDependencyCapture.Realizes CorePayloadRefinement.tables (CorePayloadRefinement.allFamilies payload)
      (CorePayloadRefinement.innerScope payload identity) (CorePayloadRefinement.innerWhole identity) ∧
    receiverAccepts (retaining identity) (CorePayloadRefinement.innerScope payload identity) [] ∧
    SourceDependencyCapture.Realizes CorePayloadRefinement.tables (CorePayloadRefinement.allFamilies payload)
      (CorePayloadRefinement.outerScope payload identity) (CorePayloadRefinement.outerWhole identity) ∧
    ¬ receiverAccepts (retaining identity) (CorePayloadRefinement.outerScope payload identity) [] := by
  dsimp only
  let payload := CorePayloadRefinement.retaining (operations := operations) (policy := policy)
    (contracts := contracts) (ports := ports) (owners := owners) identity issued
  have support : Syntax.resourceDependencies (retaining identity).dependencies = payload.retained := by
    simp [retaining, Code.dependencies, Syntax.without, Syntax.resourceDependencies, payload,
      CorePayloadRefinement.retaining_support]
  have comparison (scope : SourceDependencyCapture.Scope) :
      receiverAccepts (retaining identity) scope [] = CorePayloadRefinement.receiverCheck payload scope [] := by
    unfold receiverAccepts CorePayloadRefinement.receiverCheck
    rw [support]
    rfl
  exact ⟨CorePayloadRefinement.inner_realizes payload identity,
    by rw [comparison]; exact CorePayloadRefinement.retained_inner_receiver issued,
    CorePayloadRefinement.outer_realizes payload identity,
    by rw [comparison]; exact CorePayloadRefinement.retained_outer_receiver_rejected issued⟩
end Receivers

/-- Required retaining instance of the same helper's current transport.
Its support is computed; actual_receivers separately authenticates the inner
receiver and rejects the same payload at the outer receiver. -/
theorem retaining_helper_current [SourcePlannedChecks.DeclarationPolicy]
    (identity : Nat) (issued : identity ∈ world)
    (runtimeScope : Execution.Scope) (stack : Stack)
    (installations ambient : List Nat) (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases) (budget : Footprint)
    {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope}
    (context : Context hints)
    (certificate : SourceAdmission.Code outward actions budget phases world installations Rows.pure context)
    (certificateChecked : InstallationSupport.CodeChecked ambient outward certificate)
    (root annotated : Requirements demand)
    (run : Accounting.Run world installations Rows.pure context root)
    (entries : RecursiveRequirements.Store) (receiving : OwnerPhases.Context) (row : Footprint)
    (annotation : RowAnnotation root annotated)
    (check : Checked entries receiving phases (annotateDisposals annotated) row) (bounded : row ⊆ budget) :
    ∃ (dependencies : SourceDependencyAnnotations.Dependencies) (actualPlan : Plan dependencies)
      (actualRows : Rows (signature actualPlan)),
      CoreCallableContractSource.Supported world [] environment ScopedPorts.Support.empty
        (applyBody.subst 0 (retaining identity)) .unit actualPlan actualRows (Syntax.resourceDependencies (retaining identity).dependencies) ∧
      SourcePlannedChecks.Certified outward world actualPlan ∧
      RawStep ⟨.app applyHelper (retaining identity), runtimeScope, stack⟩ ⟨applyBody.subst 0 (retaining identity), .none, stack⟩ [] [] ∧
      ∃ actualCertificate : SourceAdmission.Code outward actions budget phases world installations actualRows context,
        InstallationSupport.CodeChecked ambient outward actualCertificate ∧
        ∃ actualRoot actualAnnotated : Requirements demand, ∃ actualRow : Footprint,
          Accounting.Run world installations actualRows context actualRoot ∧ RootTransport root actualRoot ∧
          RowAnnotation actualRoot actualAnnotated ∧
          Checked entries receiving phases (annotateDisposals actualAnnotated) actualRow ∧ actualRow ⊆ budget :=
  helper_current (retaining_source identity issued) (retaining_closed identity)
    (by simpa [retaining, Code.dependencies, Syntax.without, Syntax.resourceDependencies, List.cons_subset] using issued)
    runtimeScope stack installations ambient outward actions phases budget context certificate certificateChecked
    root annotated run entries receiving row annotation check bounded

/-- Removing the actual closed helper bind retains the current certificate and
accounting root. Its successor source comes from both_source via both_bind. -/
theorem both_current [SourcePlannedChecks.DeclarationPolicy]
    (runtimeScope : Execution.Scope) (stack : Stack)
    (installations ambient : List Nat) (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases) (budget : Footprint)
    {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope}
    (context : Context hints)
    (certificate : SourceAdmission.Code outward actions budget phases world installations bothRows context)
    (checked : InstallationSupport.CodeChecked ambient outward certificate)
    (root : Requirements demand) (run : Accounting.Run world installations bothRows context root) :
    CoreCallableContractSource.Supported world allowed environment ScopedPorts.Support.empty
      (bothBody.subst 10 applyHelper) .unit (.sequence callPlan callPlan) (sequenceRows callRows callRows) [] ∧
    SourcePlannedChecks.Certified outward world (.sequence callPlan callPlan) ∧
    RawStep ⟨both, runtimeScope, stack⟩ ⟨bothBody.subst 10 applyHelper, runtimeScope, stack⟩ [] [] ∧
    ∃ actualCertificate : SourceAdmission.Code outward actions budget phases world installations
      (sequenceRows callRows callRows) context,
      InstallationSupport.CodeChecked ambient outward actualCertificate ∧
      Accounting.Run world installations (sequenceRows callRows callRows) context root := by
  obtain ⟨afterSource, raw⟩ := both_bind (world := world) (allowed := allowed) (environment := environment) runtimeScope stack
  have supported : CoreCallableContractSource.Supported world allowed environment ScopedPorts.Support.empty
      (bothBody.subst 10 applyHelper) .unit (.sequence callPlan callPlan) (sequenceRows callRows callRows) [] := by
    refine ⟨afterSource, ?_, List.nil_subset _⟩
    apply SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mpr
    simp [bothBody, simple, sequenced, applyHelper, applyBody, Code.subst, Code.dependencies,
      Syntax.without, ScopedPorts.Support.evaluate, ScopedPorts.Support.empty]
  have certification : SourcePlannedChecks.Certified outward world (.sequence callPlan callPlan) :=
    .sequence (.sequence .pure (.sequence .pure .pure)) (.sequence .pure (.sequence .pure .pure))
  have remaining := (Accounting.silent_prefix_iff .pure Rows.pure (sequenceRows callRows callRows)).mp run
  cases certificate with
  | sequence initial body =>
    cases checked with
    | sequence initialCheck bodyCheck => exact ⟨supported, certification, raw, body, bodyCheck, remaining⟩

/-- Select checked annotations through any additional disposal alternatives.
Both actual branches remain bounded by the original current row. -/
private theorem choice_checks_at {normal : Requirements demand}
    (annotation : RowAnnotation normal annotated) :
    ∀ (left : Requirements demand) {rightDemand : List Nat} (right : Requirements rightDemand)
      (same : demand.Perm rightDemand), normal = .choice left right same →
      Checked entries receiving phases (annotateDisposals annotated) row →
    ∃ leftAnnotated rightAnnotated leftRow rightRow,
      RowAnnotation left leftAnnotated ∧ RowAnnotation right rightAnnotated ∧
      Checked entries receiving phases (annotateDisposals leftAnnotated) leftRow ∧
      Checked entries receiving phases (annotateDisposals rightAnnotated) rightRow ∧
      leftRow ⊆ row ∧ rightRow ⊆ row := by
  induction annotation generalizing row with
  | original =>
    intro left rightDemand right same equation check
    cases equation
    cases check with
    | choice leftCheck rightCheck =>
      exact ⟨_, _, _, _, .original, .original, leftCheck, rightCheck,
        List.subset_append_left _ _, List.subset_append_right _ _⟩
  | choice leftAnnotation rightAnnotation ihL ihR =>
    intro left rightDemand right same equation check
    cases equation
    cases check with
    | choice leftCheck rightCheck =>
      exact ⟨_, _, _, _, leftAnnotation, rightAnnotation, leftCheck, rightCheck,
        List.subset_append_left _ _, List.subset_append_right _ _⟩
  | alternatives normal permutation ih =>
    intro left rightDemand right same equation check
    cases check with
    | choice first second =>
      obtain ⟨a, b, ar, br, aa, ba, ac, bc, ab, bb⟩ := ih left right same equation first
      exact ⟨a, b, ar, br, aa, ba, ac, bc,
        ab.trans (List.subset_append_left _ _), bb.trans (List.subset_append_left _ _)⟩
  | sequence first second ihF ihS => intro left rightDemand right same equation; cases equation
  | emitAfter body ih => intro left rightDemand right same equation; cases equation

/-- Branch checking projects the selected alternative from the same current
accounting/check. It does not spend both alternatives or assert footprint equality.
The right alternative retains the existing permutation of owner demands. -/
theorem choice_current (choice : Bool)
    (runtimeScope : Execution.Scope) (stack : Stack)
    (world installations ambient : List Nat) (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases) (budget : Footprint)
    {scope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints scope}
    (context : Context hints) (root annotated : Requirements demand)
    (run : Accounting.Run world installations chooseRows context root)
    (entries : RecursiveRequirements.Store) (receiving : OwnerPhases.Context) (row : Footprint)
    (annotation : RowAnnotation root annotated)
    (check : Checked entries receiving phases (annotateDisposals annotated) row) (bounded : row ⊆ budget) :
    let selected := if choice then simple else sequenced
    Source world allowed environment selected action .pure Rows.pure ∧
    RawStep ⟨choose choice, runtimeScope, stack⟩ ⟨selected, runtimeScope, stack⟩ [] [] ∧
    ∃ certificate : SourceAdmission.Code outward actions budget phases world installations Rows.pure context,
      InstallationSupport.CodeChecked ambient outward certificate ∧
      ∃ selectedDemand, ∃ selectedRoot selectedAnnotated : Requirements selectedDemand, ∃ selectedRow,
        demand.Perm selectedDemand ∧ Accounting.Run world installations Rows.pure context selectedRoot ∧
        RowAnnotation selectedRoot selectedAnnotated ∧
        Checked entries receiving phases (annotateDisposals selectedAnnotated) selectedRow ∧ selectedRow ⊆ budget := by
  have branchRun := (Accounting.silent_prefix_iff .pure Rows.pure (choiceRows (first := Plan.pure) (second := Plan.pure) Rows.pure Rows.pure)).mp run
  cases branchRun with
  | choice left right same =>
    obtain ⟨leftAnnotated, rightAnnotated, leftRow, rightRow, leftAnnotation, rightAnnotation,
      leftCheck, rightCheck, leftBound, rightBound⟩ := choice_checks_at annotation _ _ same rfl check
    cases choice with
    | true =>
      obtain ⟨selected, raw⟩ := true_choice (world := world) (allowed := allowed) (environment := environment) runtimeScope stack
      exact ⟨selected, raw, .pure, .pure, _, _, _, _, .refl _, left,
        leftAnnotation, leftCheck, leftBound.trans bounded⟩
    | false =>
      obtain ⟨selected, raw⟩ := false_choice (world := world) (allowed := allowed) (environment := environment) runtimeScope stack
      exact ⟨selected, raw, .pure, .pure, _, _, _, _, same, right,
        rightAnnotation, rightCheck, rightBound.trans bounded⟩

theorem returning_closed (choice : Bool) : ClosedValue (returning choice) := by
  simp [returning, choose, simple, sequenced, ClosedValue, Code.IsValue, Code.ResourceClosed,
    Code.freeNames, Code.dependencies, Syntax.without]

theorem returning_body_certified [SourcePlannedChecks.DeclarationPolicy]
    (source : Source world [] (environment.extend 4 .unit) (choose choice) action actualPlan actualRows) :
    SourcePlannedChecks.Certified outward world actualPlan := by
  cases source with
  | branch condition yes no =>
    cases condition
    cases yes
    cases no
    exact .sequence .pure (.choice .pure .pure)

/-- Returning a callable recovers the branch body and its actual certification;
the successor remains under the same common callable result contract. -/
theorem returning_beta [SourcePlannedChecks.DeclarationPolicy] (choice : Bool)
    (runtimeScope : Execution.Scope) (stack : Stack) :
    ∃ (dependencies : SourceDependencyAnnotations.Dependencies) (actualPlan : Plan dependencies)
      (actualRows : Rows (signature actualPlan)),
      Source world [] environment (choose choice) action actualPlan actualRows ∧
      SourcePlannedChecks.Certified outward world actualPlan ∧ Refines Rows.pure actualRows ∧
      RawStep ⟨.app (returning choice) .unit, runtimeScope, stack⟩ ⟨choose choice, .none, stack⟩ [] [] := by
  obtain ⟨dependencies, plan, rows, bodySource, refinement⟩ :=
    (returning_source (world := world) (allowed := []) (environment := environment) choice).lambda_body
  have substituted := bodySource.substitution Source.unit ScopedExecution.Examples.unit_closed
  have unchanged : (choose choice).subst 4 .unit = choose choice := by simp [choose, simple, sequenced, Code.subst]
  exact ⟨dependencies, plan, rows, unchanged ▸ substituted, returning_body_certified bodySource, refinement,
    by simpa only [returning, unchanged] using
      RawStep.beta 4 (choose choice) .unit runtimeScope stack ScopedExecution.Examples.unit_closed (returning_closed choice)⟩

/-- The caller binds whichever closure the branch returns, then applies it
under that same contract. This is the caller suffix in returnedCall_source. -/
theorem selected_caller (choice : Bool) (runtimeScope : Execution.Scope) (stack : Stack) :
    let selected := if choice then simple else sequenced
    Source world [] environment (.app selected .unit) .unit callPlan callRows ∧
    RawStep ⟨.bind 12 selected (.app (.variable 12) .unit), runtimeScope, stack⟩
      ⟨.app selected .unit, runtimeScope, stack⟩ [] [] := by
  cases choice with
  | true =>
    let source : Source world [] environment (.bind 12 simple (.app (.variable 12) .unit)) .unit retainedPlan retainedRows :=
      .bind simple_source (.app (.variable (contract := action) (by simp [Environment.extend])
        (by intro identity member; cases member)) .unit (List.nil_subset _))
    simpa [Code.subst] using source.bind_step simple_closed (by simp [ClosedExcept, Code.dependencies]) runtimeScope stack
  | false =>
    let source : Source world [] environment (.bind 12 sequenced (.app (.variable 12) .unit)) .unit retainedPlan retainedRows :=
      .bind sequenced_source (.app (.variable (contract := action) (by simp [Environment.extend])
        (by intro identity member; cases member)) .unit (List.nil_subset _))
    simpa [Code.subst] using source.bind_step sequenced_closed (by simp [ClosedExcept, Code.dependencies]) runtimeScope stack

private def returnedPlain : PlainData :=
  ⟨.bind 12 (.app (.variable 12) .unit), .none, .function .unit .unit [] [], .unit, [], rfl⟩

/-- A connected actual trace includes producer beta, selection, caller binding
and invocation of the returned callable. The selected source evidence used by
beta is recovered from the branch source above, at the unchanged public contract.
The false case retains the actual additional Unit bind. -/
theorem returned_execution [SourcePlannedChecks.DeclarationPolicy] (choice : Bool) (stack : Stack) :
    Source world [] environment (returnedCall choice) .unit returnedCallPlan returnedCallRows ∧
    RawTrace ⟨returnedCall choice, .none, stack⟩ ⟨.unit, .none, stack⟩ [] [] ∧
    Source world [] environment .unit .unit .pure Rows.pure ∧
    SourcePlannedChecks.Certified outward world Plan.pure := by
  have focus : RawStep ⟨returnedCall choice, .none, stack⟩
      ⟨.app (returning choice) .unit, .none, .push (.plain returnedPlain) stack⟩ [] [] :=
    RawStep.focus returnedPlain (.bind (by simp [Code.IsValue])) stack
  obtain ⟨dependencies, plan, rows, branchSource, certification, refinement, producerBeta⟩ :=
    returning_beta (world := world) (environment := environment) (outward := outward) choice .none (.push (.plain returnedPlain) stack)
  cases choice with
  | true =>
    have selection : Source world [] environment simple action .pure Rows.pure ∧
        RawStep ⟨choose true, .none, .push (.plain returnedPlain) stack⟩
          ⟨simple, .none, .push (.plain returnedPlain) stack⟩ [] [] := by
      cases branchSource with
      | branch condition yes no =>
        exact ⟨yes.value_summary (by simp [simple, Code.IsValue]), .ifTrue simple sequenced .none _⟩
    obtain ⟨selectedSource, selectedStep⟩ := selection
    have plug := RawStep.plug returnedPlain simple simple_closed .none stack
    let caller : Source world [] environment (.bind 12 simple (.app (.variable 12) .unit)) .unit retainedPlan retainedRows :=
      .bind selectedSource (.app (.variable (contract := action) (by simp [Environment.extend])
        (by intro identity member; cases member)) .unit (List.nil_subset _))
    obtain ⟨callSource, bindStep⟩ := caller.bind_step simple_closed (by simp [ClosedExcept, Code.dependencies]) .none stack
    have boundStep : RawStep ⟨.bind 12 simple (.app (.variable 12) .unit), .none, stack⟩
        ⟨.app simple .unit, .none, stack⟩ [] [] := by simpa only [Code.subst, if_true] using bindStep
    obtain ⟨bodyDeps, bodyPlan, bodyRows, bodySource, bodyRefinement, betaStep⟩ :=
      selectedSource.beta Source.unit ScopedExecution.Examples.unit_closed simple_closed .none stack
    have finalSource : Source world [] environment .unit .unit .pure Rows.pure := by
      simpa only [simple, Code.subst] using bodySource.value_summary trivial
    have selectedBeta : RawStep ⟨.app simple .unit, .none, stack⟩ ⟨.unit, .none, stack⟩ [] [] := by
      simpa only [simple, Code.subst] using betaStep
    have trace : RawTrace ⟨returnedCall true, .none, stack⟩ ⟨.unit, .none, stack⟩ [] [] :=
      .next focus (.next producerBeta (.next selectedStep (.next plug (.next boundStep (.next selectedBeta (.refl _))))))
    exact ⟨returnedCall_source true, trace, finalSource, .pure⟩
  | false =>
    have selection : Source world [] environment sequenced action .pure Rows.pure ∧
        RawStep ⟨choose false, .none, .push (.plain returnedPlain) stack⟩
          ⟨sequenced, .none, .push (.plain returnedPlain) stack⟩ [] [] := by
      cases branchSource with
      | branch condition yes no =>
        exact ⟨no.value_summary (by simp [sequenced, Code.IsValue]), .ifFalse simple sequenced .none _⟩
    obtain ⟨selectedSource, selectedStep⟩ := selection
    have plug := RawStep.plug returnedPlain sequenced sequenced_closed .none stack
    let caller : Source world [] environment (.bind 12 sequenced (.app (.variable 12) .unit)) .unit retainedPlan retainedRows :=
      .bind selectedSource (.app (.variable (contract := action) (by simp [Environment.extend])
        (by intro identity member; cases member)) .unit (List.nil_subset _))
    obtain ⟨callSource, bindStep⟩ := caller.bind_step sequenced_closed (by simp [ClosedExcept, Code.dependencies]) .none stack
    have boundStep : RawStep ⟨.bind 12 sequenced (.app (.variable 12) .unit), .none, stack⟩
        ⟨.app sequenced .unit, .none, stack⟩ [] [] := by simpa only [Code.subst, if_true] using bindStep
    obtain ⟨bodyDeps, bodyPlan, bodyRows, bodySource, bodyRefinement, betaStep⟩ :=
      selectedSource.beta Source.unit ScopedExecution.Examples.unit_closed sequenced_closed .none stack
    have sequenceSource : Source world [] environment (.bind 3 .unit .unit) .unit bodyPlan bodyRows := by
      simpa only [sequenced, Code.subst, show ¬ (2 : Nat) = 3 by decide, ↓reduceIte] using bodySource
    have lastStep : RawStep ⟨.bind 3 .unit .unit, .none, stack⟩ ⟨.unit, .none, stack⟩ [] [] :=
      RawStep.bind 3 .unit .unit .none stack ScopedExecution.Examples.unit_closed (by simp [ClosedExcept, Code.dependencies])
    have finalSource : Source world [] environment .unit .unit .pure Rows.pure := by
      cases sequenceSource with
      | bind initial body => cases initial; cases body; exact .unit
    have selectedBeta : RawStep ⟨.app sequenced .unit, .none, stack⟩ ⟨.bind 3 .unit .unit, .none, stack⟩ [] [] := by
      simpa only [sequenced, Code.subst, show ¬ (2 : Nat) = 3 by decide, ↓reduceIte] using betaStep
    have trace : RawTrace ⟨returnedCall false, .none, stack⟩ ⟨.unit, .none, stack⟩ [] [] :=
      .next focus (.next producerBeta (.next selectedStep (.next plug (.next boundStep (.next selectedBeta (.next lastStep (.refl _)))))))
    exact ⟨returnedCall_source false, trace, finalSource, .pure⟩

#print axioms returned_execution
#print axioms retaining_helper_current
#print axioms both_current
#print axioms choice_current
#print axioms returning_beta
#print axioms selected_caller
#print axioms helper_current
#print axioms actual_receivers
#print axioms both_bind
#print axioms helper_body_certified
#print axioms helper_invocation
#print axioms true_choice
#print axioms false_choice
#print axioms retaining_supported
#print axioms chooseRetaining_supported
#print axioms false_retaining_choice
#print axioms helper_source
#print axioms both_source
#print axioms retained_source
#print axioms choose_source
#print axioms chosenCall_source
#print axioms returning_source
#print axioms returnedCall_source
end Ash.OneShot.CoreCallableContractExamples
