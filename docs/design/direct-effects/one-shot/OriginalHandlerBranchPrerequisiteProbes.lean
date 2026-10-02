import CoreCallableFiniteHandlerRegistryTransport
import OriginalHandlerSeamProbes
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
namespace Ash.OneShot.OriginalHandlerBranchPrerequisiteProbes
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract)
open CoreCallableStaticProducer CoreCallableFiniteClauseTemplate CoreCallableFiniteHandlerSource
open CoreCallableContractAdmission
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open CoreCallableReceiverRefinement (LexicalBounds)
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy
private def owners : CoreCallableContractRegistries.Owners := fun _ => none
private def policy : Syntax.TicketPolicy := fun _ => ⟨true,false⟩
private def success : Except ε α → Bool | .ok _ => true | .error _ => false
private def effect : Instance := .user 94 []
private def entries : OperationEntries := [(effect,0,Contract.integer,Contract.integer)]
private def rootClause : Template Contract.integer Contract.integer 10 [(1,Contract.integer)] (.resume 10 (.integer 42)) :=
  .resume (.integer 42)
private def declarations : Declarations entries effect Contract.integer []
    (.cons 0 1 10 (.resume 10 (.integer 42)) .nil) :=
  .cons .head rootClause [] (some []) (some []) [] [] .nil
private def rootAnnotation : Annotation entries owners [] (.perform (.user 94 []) 0 (.integer 42)) Contract.integer
    [] (.emitAfter (.request [] []) [] [⟨effect,0,false⟩]) (.sequence .pure (.request (effect := effect) (operation := 0)))
    (CoreCallableContractSource.sequenceRows Rows.pure Rows.request) := .perform .head (.integer 42)
private def graph : CoreSyntax.Graph := ⟨[
  CoreTranslation.Examples.node 0 (.integer 42) .integer,
  CoreTranslation.Examples.node 1 (.request (.user 94 []) 0 0) .integer [.user 94 []],
  CoreTranslation.Examples.node 2 (.resume 7 4 .consumed 0) .integer,
  CoreTranslation.Examples.node 3 (.handler 7 (.user 94 []) 1 [⟨0,.binder ⟨1,.integer⟩,4,2⟩]) .integer],3⟩
private def api := CoreCallableFiniteCellRegistry.original
private noncomputable def checked := CoreCallableFiniteHandlerRegistryTransport.check api declarations policy [] owners [] [] [] []

theorem exact_original_graph : CoreTranslation.translate graph = .ok
    (.handle (.user 94 []) (.perform (.user 94 []) 0 (.integer 42))
      (.cons 0 1 10 (.resume 10 (.integer 42)) .nil)) := rfl

theorem same_graph_declarations_checked : success checked = true := by decide

theorem same_graph_full_declaration_outputs :
    Nonempty (CoreCallableFiniteHandlerRegistryTransport.Result api entries policy [] owners [] [] declarations [] []) := by
  have valid := same_graph_declarations_checked
  cases actual : checked with
  | error error => simp [actual,success] at valid
  | ok receipt => exact ⟨receipt⟩

theorem all_owner_private_plan_distinct :
    (⟨rootClause.dependencies 0,rootClause.plan 0⟩ : Sigma SourceDeclarationPlans.Plan) ≠
    ⟨rootClause.dependencies 1,rootClause.plan 1⟩ := by
  intro same
  have impossible := congrArg Sigma.fst same
  simp [rootClause,Template.dependencies] at impossible

private def cellEntries : OperationEntries :=
  [(.cell 73,0,.reference 73,.integer),(.cell 73,1,.pair (.reference 73) .integer,.unit)]
private def cellClauses : Clauses := .cons 0 1 10 (.resume 10 (.integer 42))
  (.cons 1 2 11 (.resume 11 .unit) .nil)
private def cellDeclarations : Declarations cellEntries (.cell 73) Contract.integer [] cellClauses :=
  .cons .head (.resume (.integer 42)) [] (some []) (some []) [] []
    (.cons (.tail .head) (.resume .unit) [] (some []) (some []) [] [] .nil)

theorem complete_cell_checked : success
    (CoreCallableFiniteHandlerRegistryTransport.check api cellDeclarations policy [] owners [73] [] [] [73]) = true := by decide

theorem old_read_only_coverage_insufficient :
    clauseKeysCheck [(.cell 73,0,Contract.reference 73,Contract.integer)] (.cell 73)
      (.cons 0 1 10 (.resume 10 (.integer 42)) .nil) = true ∧
    CoreCallableFiniteHandlerRegistryCoverage.keysCheck [(.cell 73,0,Contract.reference 73,Contract.integer)] (.cell 73)
      (.cons 0 1 10 (.resume 10 (.integer 42)) .nil) = false := by decide

theorem missing_write_rejected : success
    (CoreCallableFiniteHandlerRegistryCoverage.check api cellEntries policy (.cell 73)
      (.cons 0 1 10 (.resume 10 (.integer 42)) .nil)) = false := by decide

theorem duplicate_rejected : CoreCallableFiniteHandlerRegistryCoverage.keysCheck entries effect
    (.cons 0 1 10 (.resume 10 (.integer 42)) (.cons 0 1 10 (.resume 10 (.integer 42)) .nil)) = false := by decide

theorem extra_cell_operation_rejected : CoreCallableFiniteHandlerRegistryCoverage.keysCheck cellEntries (.cell 73)
    (.cons 2 1 10 (.resume 10 (.integer 42)) cellClauses) = false := by decide

theorem invalid_original_schema_rejected : success (CoreCallableFiniteHandlerRegistryCoverage.check
    {api with binder := 1} cellEntries policy (.cell 73) cellClauses) = false := by decide

private def opaqueContract : Contract := .function .unit .integer [] [] (.choice .pure .pure) (Rows.choice Rows.pure Rows.pure)
private def opaqueEntries : OperationEntries := [(effect,0,opaqueContract,opaqueContract)]
private def opaqueTemplate : Template opaqueContract opaqueContract 10 [(1,opaqueContract)] (.resume 10 (.variable 1)) :=
  .resume (.variable .head)
private def opaqueDeclarations : Declarations opaqueEntries effect opaqueContract []
    (.cons 0 1 10 (.resume 10 (.variable 1)) .nil) :=
  .cons .head opaqueTemplate [] (some []) (some []) [] [] .nil

theorem whole_opaque_rows_checked : success
    (CoreCallableFiniteHandlerRegistryTransport.check api opaqueDeclarations policy [] owners [] [] [] []) = true := by decide

theorem incompatible_full_cell_record_rejected : success (CoreCallableFiniteHandlerRegistryCoverage.check api
    [(.cell 73,0,opaqueContract,Contract.integer)] policy (.cell 73) cellClauses) = false := by decide

theorem original_operation_shadow_rejected :
    (OperationRef.tail (requested := effect) (key := 0) (argument := Contract.unit) (answer := Contract.unit)
      (OperationRef.head : OperationRef [(effect,0,opaqueContract,Contract.integer)] effect 0 opaqueContract Contract.integer)).check = false := by decide

theorem original_binding_shadow_rejected :
    (BindingRef.tail (bound := 8) (value := Contract.unit)
      (BindingRef.head : BindingRef [(8,opaqueContract)] 8 opaqueContract)).check = false := by decide

private def formal : Template Contract.integer Contract.integer 10 [(1,Contract.integer)]
    (.resume 10 (.variable 1)) := .resume (.variable .head)
private def formalDeclarations (bound : List Nat) : Declarations entries effect Contract.integer []
    (.cons 0 1 10 (.resume 10 (.variable 1)) .nil) :=
  .cons .head formal bound (some []) (some []) [] [] .nil

/-- Exact current checks do not imply a fixed literal bound at a larger receiver. -/
theorem formal_receiver_boundary :
    success (checkCurrentDeclarations (formalDeclarations []) policy [] owners [73] [] [] []) = true ∧
    (formalDeclarations []).currentBoundsCheck [] [73] = false := by decide

private def unused (bound : List Nat) : Declarations entries effect Contract.integer []
    (.cons 0 1 10 (.resume 10 (.integer 42)) .nil) :=
  .cons .head rootClause bound (some []) (some []) [] [] .nil

/-- Unused literal bounds are retained; shrinking the receiver cannot erase them. -/
theorem unused_receiver_boundary :
    success (checkCurrentDeclarations (unused [73]) policy [] owners [73] [] [] [73]) = true ∧
    (unused [73]).currentBoundsCheck [] [] = false := by decide

#print axioms exact_original_graph
#print axioms same_graph_declarations_checked
#print axioms same_graph_full_declaration_outputs
#print axioms all_owner_private_plan_distinct
#print axioms complete_cell_checked
#print axioms old_read_only_coverage_insufficient
#print axioms missing_write_rejected
#print axioms duplicate_rejected
#print axioms extra_cell_operation_rejected
#print axioms invalid_original_schema_rejected
#print axioms whole_opaque_rows_checked
#print axioms incompatible_full_cell_record_rejected
#print axioms original_operation_shadow_rejected
#print axioms original_binding_shadow_rejected
#print axioms formal_receiver_boundary
#print axioms unused_receiver_boundary
end Ash.OneShot.OriginalHandlerBranchPrerequisiteProbes
