import CoreCallableClauseActualSupport
import OriginalHandlerSeamProbes
namespace Ash.OneShot.ClauseActualSupportProbes
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract)
open CoreCallableStaticProducer CoreCallableFiniteClauseTemplate CoreCallableFiniteHandlerSource
open CoreCallableContractAdmission CoreCallableClauseActualSupport CoreCallableDeliveredOperandSupport
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open CoreCallableReceiverRefinement (LexicalBounds)
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy
private def owners : CoreCallableContractRegistries.Owners := fun _ => none
private def policy : Syntax.TicketPolicy := fun _ => ⟨true,false⟩
private def storageDeclarations : Instantiation.DeclarationRegistry := fun _ => none
private def success : Except ε α → Bool | .ok _ => true | .error _ => false
private def effect : Instance := .user 94 []
private def entries : OperationEntries := [(effect,0,Contract.integer,Contract.integer)]

private def graph : CoreSyntax.Graph := ⟨[
  CoreTranslation.Examples.node 0 (.integer 42) .integer,
  CoreTranslation.Examples.node 1 (.request (.user 94 []) 0 0) .integer [.user 94 []],
  CoreTranslation.Examples.node 2 (.resume 7 4 .consumed 0) .integer,
  CoreTranslation.Examples.node 3 (.handler 7 (.user 94 []) 1 [⟨0,.binder ⟨1,.integer⟩,4,2⟩]) .integer],3⟩

private def enteredHandler : CoreMachine.State :=
  { control := .evaluate 1 .empty, frames := [.handlerBoundary 3 .empty 0], nextHandler := 1,
    observations := [.entered 3,.handlerEntered 3 0] }
private def literalBefore : CoreMachine.State :=
  { control := .evaluate 0 .empty, frames := [.request (.user 94 []) 0 .empty,.handlerBoundary 3 .empty 0], nextHandler := 1,
    observations := [.entered 3,.handlerEntered 3 0,.entered 1] }
private def literalAfter : CoreMachine.State :=
  { control := .returned (.integer 42), frames := [.request (.user 94 []) 0 .empty,.handlerBoundary 3 .empty 0], nextHandler := 1,
    observations := [.entered 3,.handlerEntered 3 0,.entered 1,.entered 0] }
private def clauseHandoff : CoreMachine.State :=
  { control := .evaluate 2 (.binding 1 (.integer 42) .empty),
    frames := [.clauseBoundary 7 4 0 0 (some [.handlerBoundary 3 .empty 0])], nextHandler := 1, nextOwner := 1,
    observations := [.entered 3,.handlerEntered 3 0,.entered 1,.entered 0,.captured 0 0] }

theorem original_initial_operand_prefix :
    CoreMachine.next graph (CoreMachine.initial graph) = .stepped enteredHandler ∧
      CoreMachine.next graph enteredHandler = .stepped literalBefore := ⟨rfl,rfl⟩

theorem original_actual_clause_handoff :
    CoreMachine.next graph literalAfter = .stepped clauseHandoff ∧
      (CoreMachine.Environment.binding 1 (.integer 42) CoreMachine.Environment.empty).lookup 1 = some (.integer 42) := ⟨rfl,rfl⟩

/-- This is the same literal runtime request handoff, on the unchanged graph.
The receiver[73] receiving probe below remains a conditional interface witness. -/
theorem actual_literal_handoff :
    CoreMachine.next graph literalBefore = .stepped literalAfter ∧
      CoreValueRelation.ValueRel graph [] literalAfter.heap (.integer 42) (.integer 42) := ⟨rfl,.integer⟩

private def operand : Annotation entries owners [] (.integer 42) Contract.integer [] (.request [] []) .pure Rows.pure := .integer 42
private def reference : OperationRef entries effect 0 Contract.integer Contract.integer := .head
private def recipe : CoreCallableStorageRecipes.Recipe := .node (some (.storage [.activation 73])) []
private def deliveredCheck (policy : Syntax.TicketPolicy) :=
  checkOperandSupport (declarations := storageDeclarations) reference operand [] Instantiation.Environment.empty recipe
    actual_literal_handoff.2 policy [] [73] [] [] [73]
private def formal : Template Contract.integer Contract.integer 10 [(1,Contract.integer)]
    (.resume 10 (.variable 1)) := .resume (.variable .head)
private def formalDeclarations (bound : List Nat) (ordinary protectedMode : Option Footprint := some []) : Declarations entries effect Contract.integer []
    (.cons 0 1 10 (.resume 10 (.variable 1)) .nil) :=
  .cons .head formal bound ordinary protectedMode [] [] .nil
private def received (bound : List Nat) (ordinary protectedMode : Option Footprint) (held : Bool) (policy : Syntax.TicketPolicy := policy) : Bool :=
  match deliveredCheck policy with
  | .error _ => false
  | .ok delivered => success (checkDeliveredDeclarations delivered CoreCallableFiniteCellRegistry.original held
      (formalDeclarations bound ordinary protectedMode))

theorem scalar_full_storage_checked : success (deliveredCheck policy) = true := by decide +kernel

theorem scalar_storage_preserved
    (delivered : DeliveredSupport storageDeclarations reference operand [] Instantiation.Environment.empty recipe
      graph [] [] (.integer 42) policy [] [73] [] [] [73]) :
    delivered.stored = .storage [73] ∧ actualSupport (.integer 42) delivered.stored = [] := by
  have accepted := delivered.storageAccepted
  simp [CoreCallableStorageRecipes.check,CoreCallableStorageRecipes.specialize,CoreCallableStorageRecipes.specializeList,
    CoreCallableStorageRecipes.contract,CoreCallableStorageRecipes.bound,CoreCallableStorageRecipes.atom,
    CoreCallableReturnStorageProducer.check,CoreCallableReturnStorageProducer.captureCheck,
    Code.dependencies, recipe] at accepted
  exact ⟨accepted.symm,rfl⟩

theorem scalar_actual_formal_ordinary : received [] (some []) (some []) false = true := by decide +kernel
theorem scalar_actual_formal_protected : received [] (some []) (some []) true = true := by decide +kernel

theorem old_whole_receiver_rejected :
    success (checkCurrentDeclarations (formalDeclarations []) policy [] owners [73] [] [] [73]) = false := by decide +kernel

theorem current_interface_receipt :
    ∃ delivered : DeliveredSupport storageDeclarations reference operand [] Instantiation.Environment.empty recipe
      graph [] [] (.integer 42) policy [] [73] [] [] [73],
    Nonempty (ReceivingReceipt CoreCallableFiniteCellRegistry.original entries policy [] owners [73] []
      (formalDeclarations []) [] [73] (selected (.cons 0 1 10 (.resume 10 (.variable 1)) .nil) 0
        (actualSupport (.integer 42) delivered.stored) [73]) 0 false) := by
  have valid := scalar_actual_formal_ordinary
  cases actual : deliveredCheck policy with
  | error error => simp [received,actual] at valid
  | ok delivered =>
      cases checked : checkDeliveredDeclarations delivered CoreCallableFiniteCellRegistry.original false (formalDeclarations []) with
      | error error => simp [received,actual,checked,success] at valid
      | ok receipt => exact ⟨delivered,⟨receipt⟩⟩

theorem unused_literal_bound_preserved : received [73,74] (some []) (some []) false = false := by decide +kernel
theorem denied_resume_rejected : received [] (some []) (some []) false (fun _ => ⟨false,false⟩) = false := by decide +kernel
theorem unavailable_ordinary_rejected : received [] none (some []) false = false := by decide +kernel
theorem unavailable_protected_rejected : received [] (some []) none true = false := by decide +kernel

theorem nearest_formal_shadows_outer :
    (LexicalBounds.extend (LexicalBounds.extend [] 1 [74]) 1 (actualSupport (.integer 42) (.storage [73]))).environment 1 = [] := rfl

theorem mismatched_delivered_code_rejected :
    ¬ CoreValueRelation.ValueRel graph [] [] (.integer 42) (.boolean true) := by
  intro related; cases related

theorem wrong_full_domain_shadow_rejected :
    (OperationRef.tail (requested := effect) (key := 0) (argument := Contract.unit) (answer := Contract.integer)
      reference).check = false := by decide +kernel

/-- Generic negative support evidence. There is no positive higher-order actual
operation handoff on the original integer-domain graph in this batch. -/
theorem actual_capture_cannot_be_omitted
    (derived : CallableContracts.Derives declarations storageEnvironment world .none code stored)
    (closed : ClosedValue code) (retained : identity ∈ Syntax.resourceDependencies code.dependencies)
    (outside : identity ∉ bound) :
    ¬ SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Bounds
      ((lexical : LexicalBounds).extend parameter (actualSupport code stored)).environment
      (Code.resume binder (.variable parameter)).dependencies bound := by
  rw [formal_resume_bound_iff]
  exact captured_identity_required derived closed retained outside

#print axioms original_initial_operand_prefix
#print axioms original_actual_clause_handoff
#print axioms actual_literal_handoff
#print axioms scalar_full_storage_checked
#print axioms scalar_storage_preserved
#print axioms scalar_actual_formal_ordinary
#print axioms scalar_actual_formal_protected
#print axioms old_whole_receiver_rejected
#print axioms current_interface_receipt
#print axioms unused_literal_bound_preserved
#print axioms denied_resume_rejected
#print axioms unavailable_ordinary_rejected
#print axioms unavailable_protected_rejected
#print axioms nearest_formal_shadows_outer
#print axioms mismatched_delivered_code_rejected
#print axioms wrong_full_domain_shadow_rejected
#print axioms actual_capture_cannot_be_omitted
end Ash.OneShot.ClauseActualSupportProbes
