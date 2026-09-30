import CoreCallablePlanRefinement

/-! Bounded DN-0033 contextual callable refinement. The interface transports
existing static certificates and exact-root accounting, without runtime success,
Source/Auth, execution-site or Valid premises. Authenticated payload BODY evidence
then constructs current post-beta admission. Pre-beta callable/application
admission, heterogeneous joins, higher-order results, general effectful contract
inference and whole-program InitialAdmission remain separate obligations. -/
namespace Ash.OneShot.CoreCallableRefinementTransport
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlanSignatures (Signature signature)
open SourceDependencyAnnotations (Dependencies)
open SourceDependencyChecks.Lexical (ReturnHints)
open RecursiveRequirements (Requirements)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open CorePayloadRefinement (Payload PurePlan)

/-- All contexts and current checking parameters are quantified. In particular,
the checked field follows this interface's exact transported certificate, and
accounting preserves the literal root requirements. -/
structure Refines {contractDependencies actualDependencies : Dependencies}
    {contractSignature : Signature contractDependencies} {actualSignature : Signature actualDependencies}
    (contractRows : Rows contractSignature) (actualRows : Rows actualSignature) : Prop where
  code : ∀ (outward : List Instance) (actions : Syntax.UsageTickets) (budget : Footprint)
      (phases : OwnerPhaseTransitions.Phases) (world installations : List Nat)
      {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope} (context : Context hints),
      SourceAdmission.Code outward actions budget phases world installations contractRows context →
      SourceAdmission.Code outward actions budget phases world installations actualRows context
  checked : ∀ (ambient : List Nat) (outward : List Instance) (actions : Syntax.UsageTickets)
      (budget : Footprint) (phases : OwnerPhaseTransitions.Phases) (world installations : List Nat)
      {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope} (context : Context hints)
      (certificate : SourceAdmission.Code outward actions budget phases world installations contractRows context),
      InstallationSupport.CodeChecked ambient outward certificate →
      InstallationSupport.CodeChecked ambient outward
        (code outward actions budget phases world installations context certificate)
  accounting : ∀ (world installations : List Nat)
      {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope} (context : Context hints)
      {demand : List Nat} (root : Requirements demand),
      Accounting.Run world installations contractRows context root →
      Accounting.Run world installations actualRows context root

namespace Refines
variable {firstDependencies middleDependencies lastDependencies : Dependencies}
  {firstSignature : Signature firstDependencies} {middleSignature : Signature middleDependencies}
  {lastSignature : Signature lastDependencies}
  {firstRows : Rows firstSignature} {middleRows : Rows middleSignature} {lastRows : Rows lastSignature}

theorem identity (rows : Rows firstSignature) : Refines rows rows where
  code := by intros; assumption
  checked := by intros; assumption
  accounting := by intros; assumption

theorem compose (first : Refines firstRows middleRows) (second : Refines middleRows lastRows) :
    Refines firstRows lastRows where
  code := by
    intro outward actions budget phases world installations scope hints context certificate
    exact second.code outward actions budget phases world installations context
      (first.code outward actions budget phases world installations context certificate)
  checked := by
    intro ambient outward actions budget phases world installations scope hints context certificate checked
    exact second.checked ambient outward actions budget phases world installations context _
      (first.checked ambient outward actions budget phases world installations context certificate checked)
  accounting := by
    intro world installations scope hints context demand root run
    exact second.accounting world installations context root
      (first.accounting world installations context root run)

/-- Actual structural pure/sequence rows refine the common pure contract. -/
theorem pure_plan {plan : SourceDeclarationPlans.Plan actualDependencies}
    (structural : PurePlan plan) (rows : Rows (signature plan)) : Refines Rows.pure rows where
  code := by
    intro outward actions budget phases world installations scope hints context _certificate
    exact CoreCallablePlanRefinement.admission structural rows context
  checked := by
    intro ambient outward actions budget phases world installations scope hints context certificate _checked
    exact CoreCallablePlanRefinement.admission_checked structural rows context
  accounting := by
    intro world installations scope hints context demand root run
    exact (CoreCallablePlanRefinement.accounting_iff structural rows context root).mpr run

/-- Insert a structural pure prefix before any suffix, including effect requests,
cleanup and owner transfer rows. The actual suffix is preserved verbatim. -/
theorem pure_prefix {plan : SourceDeclarationPlans.Plan actualDependencies}
    (structural : PurePlan plan) (prefixRows : Rows (signature plan))
    (suffixRows : Rows firstSignature) : Refines suffixRows (.sequence prefixRows suffixRows) where
  code := by
    intro outward actions budget phases world installations scope hints context certificate
    exact .sequence (CoreCallablePlanRefinement.admission structural prefixRows (.plain suffixRows context)) certificate
  checked := by
    intro ambient outward actions budget phases world installations scope hints context certificate checked
    exact .sequence (CoreCallablePlanRefinement.admission_checked structural prefixRows (.plain suffixRows context)) checked
  accounting := by
    intro world installations scope hints context demand root run
    exact (Accounting.silent_prefix_iff (CoreCallablePlanRefinement.silent structural) prefixRows suffixRows).mpr run
end Refines

variable {operations : SourcePlannedTyping.Operations} {policy : Syntax.TicketPolicy}
  {contracts : SourcePlannedTyping.Contracts} {ports : OperationRows operations}
  {owners : ContractRows contracts} {world installations ambient : List Nat}
  {outward : List Instance} {actions : Syntax.UsageTickets} {budget : Footprint}
  {phases : OwnerPhaseTransitions.Phases}
  {tables : CallableProtectionFrames.Tables} {families : SourceDependencyFrames.Families}
  {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope}
  {contractDependencies : Dependencies} {contractSignature : Signature contractDependencies}

/-- The constructed current post-beta fields, with their actual body rows.
This is a result abbreviation, not an input evidence or execution premise. -/
def PostBeta (payload : Payload operations policy contracts ports owners world)
    (context : Context hints) (stack : Stack) (root : Requirements demand)
    (runtimeScope : Execution.Scope) : Prop :=
    ∃ admitted : SourceAdmission.Admitted operations policy contracts ports owners
        (fun _ => none) CorePayloadRefinement.baseRows world installations [] outward .none
        actions phases budget tables families context stack (payload.body.subst 2 .unit)
        .unit [] payload.requirements (signature payload.plan) .unit payload.rows,
      InstallationSupport.CodeChecked ambient outward admitted.certificate ∧
      Accounting.Run world installations payload.rows context root ∧
      RawStep ⟨.app payload.code .unit, runtimeScope, stack⟩
        ⟨payload.body.subst 2 .unit, .none, stack⟩ [] []

/-- Actual BODY Source/Auth is obtained by existing Unit substitution. Current
contract certificates and actual receiving-stack evidence suffice for current
post-beta admission; no successor admission or ExecutionSite is assumed. -/
theorem payload_post_beta (payload : Payload operations policy contracts ports owners world)
    (contractRows : Rows contractSignature) (refinement : Refines contractRows payload.rows)
    (context : Context hints) (stack : Stack)
    (receiving : Context.Source operations.erase policy contracts.erase tables families world context stack)
    (certificate : SourceAdmission.Code outward actions budget phases world installations contractRows context)
    (checked : InstallationSupport.CodeChecked ambient outward certificate)
    (root : Requirements demand) (accounted : Accounting.Run world installations contractRows context root)
    (runtimeScope : Execution.Scope) :
    ∃ admitted : SourceAdmission.Admitted operations policy contracts ports owners
        (fun _ => none) CorePayloadRefinement.baseRows world installations [] outward .none
        actions phases budget tables families context stack (payload.body.subst 2 .unit)
        .unit [] payload.requirements (signature payload.plan) .unit payload.rows,
      InstallationSupport.CodeChecked ambient outward admitted.certificate ∧
      Accounting.Run world installations payload.rows context root ∧
      RawStep ⟨.app payload.code .unit, runtimeScope, stack⟩
        ⟨payload.body.subst 2 .unit, .none, stack⟩ [] [] := by
  obtain ⟨source, authenticated⟩ := payload.invocation
  let actualCertificate := refinement.code outward actions budget phases world installations context certificate
  let admitted := SourceAdmission.Admitted.of_source source authenticated actualCertificate receiving
  exact ⟨admitted, refinement.checked ambient outward actions budget phases world installations context certificate checked,
    refinement.accounting world installations context root accounted, payload.beta runtimeScope stack⟩

/-- All three retained payload constructors specialize this same public pure
contract through their private actual body rows. -/
theorem pure_payload_post_beta (payload : Payload operations policy contracts ports owners world)
    (context : Context hints) (stack : Stack)
    (receiving : Context.Source operations.erase policy contracts.erase tables families world context stack)
    (certificate : SourceAdmission.Code outward actions budget phases world installations Rows.pure context)
    (checked : InstallationSupport.CodeChecked ambient outward certificate)
    (root : Requirements demand) (accounted : Accounting.Run world installations Rows.pure context root)
    (runtimeScope : Execution.Scope) :
    ∃ admitted : SourceAdmission.Admitted operations policy contracts ports owners
        (fun _ => none) CorePayloadRefinement.baseRows world installations [] outward .none
        actions phases budget tables families context stack (payload.body.subst 2 .unit)
        .unit [] payload.requirements (signature payload.plan) .unit payload.rows,
      InstallationSupport.CodeChecked ambient outward admitted.certificate ∧
      Accounting.Run world installations payload.rows context root ∧
      RawStep ⟨.app payload.code .unit, runtimeScope, stack⟩
        ⟨payload.body.subst 2 .unit, .none, stack⟩ [] [] :=
  payload_post_beta payload Rows.pure (Refines.pure_plan payload.structural payload.rows)
    context stack receiving certificate checked root accounted runtimeScope

/-- Different unchanged Unit/sequence bodies receive admission from one pure
contract at the same current receiving context and declared callable port. -/
theorem two_bodies_post_beta
    (context : Context hints) (stack : Stack)
    (receiving : Context.Source operations.erase policy contracts.erase tables families world context stack)
    (certificate : SourceAdmission.Code outward actions budget phases world installations Rows.pure context)
    (checked : InstallationSupport.CodeChecked ambient outward certificate)
    (root : Requirements demand) (accounted : Accounting.Run world installations Rows.pure context root)
    (runtimeScope : Execution.Scope) :
    let trivial : Payload operations policy contracts ports owners world := CorePayloadRefinement.trivial
    let sequenced : Payload operations policy contracts ports owners world := CorePayloadRefinement.sequenced
    PostBeta (installations := installations) (ambient := ambient) (outward := outward)
      (actions := actions) (phases := phases) (budget := budget) (tables := tables) (families := families)
      trivial context stack root runtimeScope ∧
    PostBeta (installations := installations) (ambient := ambient) (outward := outward)
      (actions := actions) (phases := phases) (budget := budget) (tables := tables) (families := families)
      sequenced context stack root runtimeScope ∧
    trivial.value.erase.erase.port = ScopedPorts.Port.function .unit .unit [] ∧
    sequenced.value.erase.erase.port = ScopedPorts.Port.function .unit .unit [] := by
  dsimp only
  exact ⟨pure_payload_post_beta _ context stack receiving certificate checked root accounted runtimeScope,
    pure_payload_post_beta _ context stack receiving certificate checked root accounted runtimeScope,
    Payload.exact_port _, Payload.exact_port _⟩

/-- Retention is still computed and historically issued, and actual receiving
cuts accept/reject it independently of the post-beta row transport. In
particular this theorem supplies no pre-beta capture/application admission
for the rejected receiver. -/
theorem retaining_post_beta_and_receivers (identity : Nat) (issued : identity ∈ world)
    (context : Context hints) (stack : Stack)
    (receiving : Context.Source operations.erase policy contracts.erase tables families world context stack)
    (certificate : SourceAdmission.Code outward actions budget phases world installations Rows.pure context)
    (checked : InstallationSupport.CodeChecked ambient outward certificate)
    (root : Requirements demand) (accounted : Accounting.Run world installations Rows.pure context root)
    (runtimeScope : Execution.Scope) :
    let payload : Payload operations policy contracts ports owners world := CorePayloadRefinement.retaining identity issued
    PostBeta (installations := installations) (ambient := ambient) (outward := outward)
      (actions := actions) (phases := phases) (budget := budget) (tables := tables) (families := families)
      payload context stack root runtimeScope ∧
    payload.value.erase.erase.port = ScopedPorts.Port.function .unit .unit [] ∧
    payload.retained = [identity] ∧ payload.retained ⊆ world ∧
    CorePayloadRefinement.checkReceiver payload (CorePayloadRefinement.innerScope payload identity) [] = true ∧
    CorePayloadRefinement.checkReceiver payload (CorePayloadRefinement.outerScope payload identity) [] = false := by
  dsimp only
  exact ⟨pure_payload_post_beta _ context stack receiving certificate checked root accounted runtimeScope,
    Payload.exact_port _, CorePayloadRefinement.retaining_support issued, Payload.retained_issued _,
    CorePayloadRefinement.retaining_receiver_checked issued, CorePayloadRefinement.retaining_receiver_rejected issued⟩

/- This checkpoint builds SourceAdmission.Admitted for the actual substituted
body and its exact certificate, with current-world/receiver Source evidence.
The old pre-beta lambda guard and fixed rich application/body metadata remain
unchanged. A pure-plan refinement does not authenticate capture receipt, erase
retention, infer general effectful contracts, type homogeneous closure joins or
transport higher-order result refinements through caller continuations. Those
interfaces and whole InitialAdmission remain open. -/

#print axioms Refines.identity
#print axioms Refines.compose
#print axioms Refines.pure_plan
#print axioms Refines.pure_prefix
#print axioms payload_post_beta
#print axioms pure_payload_post_beta
#print axioms two_bodies_post_beta
#print axioms retaining_post_beta_and_receivers
end Ash.OneShot.CoreCallableRefinementTransport
