import CoreCallableRefinementTransport

/-! Bounded DN-0033 checked-root transport. Normal requirement structure may
change while its owner-demand index and current checking budget stay fixed.
Choice checks alternatives at the same phases; it never consumes both branches
sequentially or asserts equality of their concatenated footprint to the original.
This is not callable value typing, execution preservation or whole M4 validity. -/
namespace Ash.OneShot.CoreCallableRootRefinement
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlanSignatures (Signature signature)
open SourceDependencyAnnotations (Dependencies RowAnnotation)
open SourceDependencyChecks.Lexical (ReturnHints)
open RecursiveRequirements (Requirements Checked)
open SourceScheduledCleanupInterfaces.Lexical.Recursive (annotateDisposals)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual

/-- Construct actual annotation/check/bound evidence from arbitrary current
contract evidence. Both normal roots have the exact same owner-demand index. -/
structure RootTransport {demand : List Nat} (normal actual : Requirements demand) : Prop where
  checked : ∀ (entries : RecursiveRequirements.Store) (receiving : OwnerPhases.Context)
      (phases : OwnerPhaseTransitions.Phases) (budget : Footprint)
      {annotated : Requirements demand} {row : Footprint},
      RowAnnotation normal annotated → Checked entries receiving phases (annotateDisposals annotated) row →
      row ⊆ budget →
      ∃ actualAnnotated : Requirements demand, ∃ actualRow : Footprint,
        RowAnnotation actual actualAnnotated ∧
        Checked entries receiving phases (annotateDisposals actualAnnotated) actualRow ∧ actualRow ⊆ budget

namespace RootTransport
variable {demand : List Nat} {normal middle last left right : Requirements demand}

theorem identity (root : Requirements demand) : RootTransport root root where
  checked := by
    intro entries receiving phases budget annotated row annotation checked bounded
    exact ⟨annotated, row, annotation, checked, bounded⟩

theorem compose (first : RootTransport normal middle) (second : RootTransport middle last) :
    RootTransport normal last where
  checked := by
    intro entries receiving phases budget annotated row annotation checked bounded
    obtain ⟨intermediate, intermediateRow, annotationMiddle, checkMiddle, boundMiddle⟩ :=
      first.checked entries receiving phases budget annotation checked bounded
    exact second.checked entries receiving phases budget annotationMiddle checkMiddle boundMiddle

/-- The two checks use the same store, receiver and phases. Their footprints
may duplicate entries, but set inclusion still bounds their append by the same
budget. The returned normal and annotated roots retain both actual alternatives. -/
theorem choice (first : RootTransport normal left) (second : RootTransport normal right) :
    RootTransport normal (.choice left right (.refl demand)) where
  checked := by
    intro entries receiving phases budget annotated row annotation checked bounded
    obtain ⟨leftAnnotated, leftRow, leftAnnotation, leftCheck, leftBound⟩ :=
      first.checked entries receiving phases budget annotation checked bounded
    obtain ⟨rightAnnotated, rightRow, rightAnnotation, rightCheck, rightBound⟩ :=
      second.checked entries receiving phases budget annotation checked bounded
    exact ⟨.choice leftAnnotated rightAnnotated (.refl demand), leftRow ++ rightRow,
      .choice leftAnnotation rightAnnotation,
      by simpa only [annotateDisposals] using Checked.choice leftCheck rightCheck,
      List.append_subset.mpr ⟨leftBound, rightBound⟩⟩
end RootTransport

/-- The exact existing certificate interface, with accounting allowed to
construct an actual normal root and its checked-root transport. No Source/Auth,
execution, successor or Valid field appears here. -/
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
      ∃ actualRoot : Requirements demand,
        Accounting.Run world installations actualRows context actualRoot ∧ RootTransport root actualRoot

namespace Refines
variable {firstDependencies middleDependencies lastDependencies : Dependencies}
  {firstSignature : Signature firstDependencies} {middleSignature : Signature middleDependencies}
  {lastSignature : Signature lastDependencies}
  {firstRows : Rows firstSignature} {middleRows : Rows middleSignature} {lastRows : Rows lastSignature}

theorem identity (rows : Rows firstSignature) : Refines rows rows where
  code := by intros; assumption
  checked := by intros; assumption
  accounting := by
    intro world installations scope hints context demand root run
    exact ⟨root, run, RootTransport.identity root⟩

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
    obtain ⟨middleRoot, middleRun, firstTransport⟩ := first.accounting world installations context root run
    obtain ⟨actualRoot, actualRun, secondTransport⟩ := second.accounting world installations context middleRoot middleRun
    exact ⟨actualRoot, actualRun, firstTransport.compose secondTransport⟩

/-- Every previous identical-root refinement embeds with identity root
transport; none of its existing contextual certificate evidence is weakened. -/
theorem of_exact (exact : CoreCallableRefinementTransport.Refines firstRows middleRows) :
    Refines firstRows middleRows where
  code := exact.code
  checked := exact.checked
  accounting := by
    intro world installations scope hints context demand root run
    exact ⟨root, exact.accounting world installations context root run, RootTransport.identity root⟩

/-- A choice retains two separately checked actual roots of one contract.
Accounting.Run.choice keeps the same demand, not the concatenated demands of
sequential execution. Its root transport supplies current budget evidence. -/
theorem choice (first : Refines firstRows middleRows) (second : Refines firstRows lastRows) :
    Refines firstRows (.choice middleRows lastRows) where
  code := by
    intro outward actions budget phases world installations scope hints context certificate
    exact .choice (first.code outward actions budget phases world installations context certificate)
      (second.code outward actions budget phases world installations context certificate)
  checked := by
    intro ambient outward actions budget phases world installations scope hints context certificate checked
    exact .choice (first.checked ambient outward actions budget phases world installations context certificate checked)
      (second.checked ambient outward actions budget phases world installations context certificate checked)
  accounting := by
    intro world installations scope hints context demand root run
    obtain ⟨leftRoot, leftRun, leftTransport⟩ := first.accounting world installations context root run
    obtain ⟨rightRoot, rightRun, rightTransport⟩ := second.accounting world installations context root run
    exact ⟨.choice leftRoot rightRoot (.refl demand), .choice leftRun rightRun (.refl demand),
      leftTransport.choice rightTransport⟩
end Refines

/-- Expose the constructive accounting/annotation/check results together. The
same current budget, store, receiver and phases check both alternatives. -/
theorem checked_accounting {contractDependencies actualDependencies : Dependencies}
    {contractSignature : Signature contractDependencies} {actualSignature : Signature actualDependencies}
    {contractRows : Rows contractSignature} {actualRows : Rows actualSignature}
    (refinement : Refines contractRows actualRows)
    (world installations : List Nat) {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope}
    (context : Context hints) (root annotated : Requirements demand)
    (run : Accounting.Run world installations contractRows context root)
    (entries : RecursiveRequirements.Store) (receiving : OwnerPhases.Context)
    (phases : OwnerPhaseTransitions.Phases) (budget row : Footprint)
    (annotation : RowAnnotation root annotated)
    (checked : Checked entries receiving phases (annotateDisposals annotated) row) (bounded : row ⊆ budget) :
    ∃ actualRoot actualAnnotated : Requirements demand, ∃ actualRow : Footprint,
      Accounting.Run world installations actualRows context actualRoot ∧
      RootTransport root actualRoot ∧ RowAnnotation actualRoot actualAnnotated ∧
      Checked entries receiving phases (annotateDisposals actualAnnotated) actualRow ∧ actualRow ⊆ budget := by
  obtain ⟨actualRoot, actualRun, transport⟩ := refinement.accounting world installations context root run
  obtain ⟨actualAnnotated, actualRow, actualAnnotation, actualCheck, actualBound⟩ :=
    transport.checked entries receiving phases budget annotation checked bounded
  exact ⟨actualRoot, actualAnnotated, actualRow, actualRun, transport, actualAnnotation, actualCheck, actualBound⟩

variable {operations : SourcePlannedTyping.Operations} {policy : Syntax.TicketPolicy}
  {contracts : SourcePlannedTyping.Contracts} {ports : OperationRows operations}
  {owners : ContractRows contracts} {world : List Nat}

/-- Unit, sequence and retaining payload rows all have the same contract. This
constructor is generic over any two supplied actual structural payloads. -/
theorem payload_choice (left right : CorePayloadRefinement.Payload operations policy contracts ports owners world) :
    Refines Rows.pure (.choice left.rows right.rows) :=
  (Refines.of_exact (CoreCallableRefinementTransport.Refines.pure_plan left.structural left.rows)).choice
    (Refines.of_exact (CoreCallableRefinementTransport.Refines.pure_plan right.structural right.rows))

/-- Concrete distinct unchanged bodies at arbitrary continuation: their private
actual rows share the contract, but their accounting root can gain a choice. -/
theorem unit_sequence_choice :
    Refines Rows.pure (.choice
      (CorePayloadRefinement.trivial (operations := operations) (policy := policy)
        (contracts := contracts) (ports := ports) (owners := owners) (world := world)).rows
      (CorePayloadRefinement.sequenced (operations := operations) (policy := policy)
        (contracts := contracts) (ports := ports) (owners := owners) (world := world)).rows) :=
  payload_choice _ _

theorem unit_retaining_choice (identity : Nat) (issued : identity ∈ world) :
    Refines Rows.pure (.choice
      (CorePayloadRefinement.trivial (operations := operations) (policy := policy)
        (contracts := contracts) (ports := ports) (owners := owners) (world := world)).rows
      (CorePayloadRefinement.retaining (operations := operations) (policy := policy)
        (contracts := contracts) (ports := ports) (owners := owners) identity issued).rows) :=
  payload_choice _ _

/- Retain this checked-root prerequisite, not a common Source.branch result or
an old lambda/application coercion. No target code, declared port, support or
source/authenticated body evidence is changed. Receiving resources, returned
closures, saved continuations, resource exit and whole InitialAdmission remain
separate obligations. General effectful contract inference is not supplied. -/

#print axioms RootTransport.identity
#print axioms RootTransport.compose
#print axioms RootTransport.choice
#print axioms Refines.identity
#print axioms Refines.compose
#print axioms Refines.of_exact
#print axioms Refines.choice
#print axioms checked_accounting
#print axioms payload_choice
#print axioms unit_sequence_choice
#print axioms unit_retaining_choice
end Ash.OneShot.CoreCallableRootRefinement
