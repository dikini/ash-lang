import CorePayloadRefinement

/-! Bounded DN-0033 callable-contract experiment. Actual pure/sequence body
plans receive existing M4 static certificates at every current context and keep
exact root accounting. Body code, declared ports and observable events are not
rewritten. This supplies no coercion for the old rich lambda/application/result
judgments and is not a whole-program admission or effectful-contract theorem. -/
namespace Ash.OneShot.CoreCallablePlanRefinement
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies)
open SourceDependencyChecks.Lexical (ReturnHints)
open RecursiveRequirements (Requirements)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open CorePayloadRefinement (PurePlan Payload)

variable {dependencies : Dependencies} {plan : Plan dependencies}
  {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope}
  {outward : List Instance} {actions : Syntax.UsageTickets} {budget : Footprint}
  {phases : OwnerPhaseTransitions.Phases} {world installations ambient : List Nat}

/-- Construct the actual row certificate rather than an erased pure body.
    Sequence prefixes are checked at their real pending-tail context. -/
theorem admission (structural : PurePlan plan) (rows : Rows (signature plan))
    (context : Context hints) :
    SourceAdmission.Code outward actions budget phases world installations rows context := by
  induction structural generalizing scope with
  | pure => cases rows; exact .pure
  | sequence first second ihFirst ihSecond =>
    cases rows with
    | sequence firstRows secondRows =>
      exact .sequence (ihFirst firstRows _) (ihSecond secondRows context)

/-- The installation-support judgment checks the exact constructed certificate;
    it does not merely assert that some decoration at the declared port exists. -/
theorem admission_checked (structural : PurePlan plan) (rows : Rows (signature plan))
    (context : Context hints) :
    InstallationSupport.CodeChecked ambient outward
      (admission (outward := outward) (actions := actions) (budget := budget)
        (phases := phases) (world := world) (installations := installations) structural rows context) := by
  induction structural generalizing scope with
  | pure => cases rows; exact .pure
  | sequence first second ihFirst ihSecond =>
    cases rows with
    | sequence firstRows secondRows =>
      exact .sequence (ihFirst firstRows _) (ihSecond secondRows context)

/-- Structural silence is an existing dependency predicate, not an assumption
    that a computation executes successfully or has no retained resources. -/
theorem silent (structural : PurePlan plan) : dependencies.Silent := by
  induction structural with
  | pure => exact .pure
  | sequence first second ihFirst ihSecond => exact .sequence ihFirst ihSecond

/-- Exact root transport, for arbitrary saved frames, owners, cleanup callbacks,
    installations and worlds. Accounting still checks the same continuation. -/
theorem accounting_iff (structural : PurePlan plan) (rows : Rows (signature plan))
    (context : Context hints) (root : Requirements demand) :
    Accounting.Run world installations rows context root ↔
      Accounting.Run world installations Rows.pure context root := by
  exact (Accounting.silent_iff (silent structural) rows).trans
    (Accounting.silent_iff (dependencies := .pure) .pure Rows.pure).symm

/-- Equivalent public-contract formulation with an ordinary continuation. -/
theorem accounting_wait_iff (structural : PurePlan plan) (rows : Rows (signature plan))
    (context : Context hints) (root : Requirements demand) :
    Accounting.Run world installations rows context root ↔
      Accounting.Wait world installations context .ordinary root :=
  Accounting.silent_iff (silent structural) rows

variable {operations : SourcePlannedTyping.Operations} {policy : Syntax.TicketPolicy}
  {contracts : SourcePlannedTyping.Contracts} {ports : OperationRows operations}
  {owners : ContractRows contracts}

/-- Each authenticated payload's actual body rows supply the same pure contract.
    Its body Source/Auth evidence and computed support remain in Payload; none is
    replaced by the contract certificate. -/
theorem payload_static_contract (payload : Payload operations policy contracts ports owners world)
    (context : Context hints) (root : Requirements demand) :
    ∃ certificate : SourceAdmission.Code outward actions budget phases world installations payload.rows context,
      InstallationSupport.CodeChecked ambient outward certificate ∧
      (Accounting.Run world installations Rows.pure context root ↔
        Accounting.Run world installations payload.rows context root) := by
  exact ⟨admission payload.structural payload.rows context,
    admission_checked payload.structural payload.rows context,
    (accounting_iff payload.structural payload.rows context root).symm⟩

/-- Both distinct unchanged bodies have contextual certificates and exact-root
    refinements at the same arbitrary receiver. -/
theorem two_bodies_same_contract (context : Context hints) (root : Requirements demand) :
    ∃ first : SourceAdmission.Code outward actions budget phases world installations
        (CorePayloadRefinement.trivial (operations := operations) (policy := policy)
          (contracts := contracts) (ports := ports) (owners := owners) (world := world)).rows context,
      ∃ second : SourceAdmission.Code outward actions budget phases world installations
        (CorePayloadRefinement.sequenced (operations := operations) (policy := policy)
          (contracts := contracts) (ports := ports) (owners := owners) (world := world)).rows context,
        InstallationSupport.CodeChecked ambient outward first ∧
        InstallationSupport.CodeChecked ambient outward second ∧
        (Accounting.Run world installations Rows.pure context root ↔
          Accounting.Run world installations
            (CorePayloadRefinement.trivial (operations := operations) (policy := policy)
              (contracts := contracts) (ports := ports) (owners := owners) (world := world)).rows context root) ∧
        (Accounting.Run world installations Rows.pure context root ↔
          Accounting.Run world installations
            (CorePayloadRefinement.sequenced (operations := operations) (policy := policy)
              (contracts := contracts) (ports := ports) (owners := owners) (world := world)).rows context root) := by
  obtain ⟨first, checkedFirst, accountsFirst⟩ := payload_static_contract
    (CorePayloadRefinement.trivial (operations := operations) (policy := policy)
      (contracts := contracts) (ports := ports) (owners := owners) (world := world)) context root
  obtain ⟨second, checkedSecond, accountsSecond⟩ := payload_static_contract
    (CorePayloadRefinement.sequenced (operations := operations) (policy := policy)
      (contracts := contracts) (ports := ports) (owners := owners) (world := world)) context root
  exact ⟨first, second, checkedFirst, checkedSecond, accountsFirst, accountsSecond⟩

/-- The retained-cell body has the same accounting contract, but its independent
    support still admits the actual inner receiver and rejects the outer one.
    In particular, a universal pure-plan certificate alone is not payload escape
    authorization. The declared function request row stays exactly empty. -/
theorem retaining_contract_and_receivers (identity : Nat) (issued : identity ∈ world)
    (context : Context hints) (root : Requirements demand) :
    let payload : Payload operations policy contracts ports owners world :=
      CorePayloadRefinement.retaining identity issued
    (∃ certificate : SourceAdmission.Code outward actions budget phases world installations payload.rows context,
      InstallationSupport.CodeChecked ambient outward certificate ∧
      (Accounting.Run world installations Rows.pure context root ↔
        Accounting.Run world installations payload.rows context root)) ∧
    payload.value.erase.erase.port = ScopedPorts.Port.function .unit .unit [] ∧
    payload.retained = [identity] ∧ payload.retained ⊆ world ∧
    CorePayloadRefinement.checkReceiver payload (CorePayloadRefinement.innerScope payload identity) [] = true ∧
    CorePayloadRefinement.checkReceiver payload (CorePayloadRefinement.outerScope payload identity) [] = false := by
  dsimp only
  exact ⟨payload_static_contract _ context root, Payload.exact_port _,
    CorePayloadRefinement.retaining_support issued, Payload.retained_issued _,
    CorePayloadRefinement.retaining_receiver_checked issued,
    CorePayloadRefinement.retaining_receiver_rejected issued⟩

/- The generic payload specialization includes the cell-retaining body. Its
    retention remains computed from unchanged closed code and historically
    issued, and the actual cut-based receiver check still rejects an outside
    owner. These certificates do not turn that check into an old lambda Auth.

    Remaining interfaces: ValueRows.function and Auth.app still fix one actual
    body decoration; old Source.lambda fixes its rich signature and latent row;
    old Auth.lambda still bounds captures by declared port/request resources;
    Source/Auth.branch require a homogeneous rich result. A public contract
    must be transported through those judgments, substitution, selected clause
    input, higher-order results/resume/bind continuations and resource exit.
    This leaf proves the pure/sequence accounting refinement only. Effectful
    callable contracts and whole InitialAdmission.Program remain unconstructed. -/

#print axioms admission
#print axioms admission_checked
#print axioms silent
#print axioms accounting_iff
#print axioms accounting_wait_iff
#print axioms payload_static_contract
#print axioms two_bodies_same_contract
#print axioms retaining_contract_and_receivers

end Ash.OneShot.CoreCallablePlanRefinement
