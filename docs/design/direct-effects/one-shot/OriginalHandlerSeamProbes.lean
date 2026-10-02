import CoreCallableFiniteHandlerSource
namespace Ash.OneShot.OriginalHandlerSeamProbes
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
private def success : Except Error α → Bool | .ok _ => true | .error _ => false
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
private def rootCheck := CoreCallableFiniteHandlerSource.check rootAnnotation declarations policy [] [] [] [] .none [] []

private def graph : CoreSyntax.Graph := ⟨[
  CoreTranslation.Examples.node 0 (.integer 42) .integer,
  CoreTranslation.Examples.node 1 (.request (.user 94 []) 0 0) .integer [.user 94 []],
  CoreTranslation.Examples.node 2 (.resume 7 4 .consumed 0) .integer,
  CoreTranslation.Examples.node 3 (.handler 7 (.user 94 []) 1 [⟨0,.binder ⟨1,.integer⟩,4,2⟩]) .integer],3⟩


private def currentCheck := checkCurrentDeclarations declarations policy [] owners [] [] [] []
theorem original_declaration_current_checked : success currentCheck = true := by decide

theorem original_current_full_outputs :
    Nonempty (CurrentDeclarationReceipt entries policy [] owners [] [] declarations [] []) := by
  have valid := original_declaration_current_checked
  cases actual : currentCheck with
  | error error => simp [actual,success] at valid
  | ok receipt => exact ⟨receipt⟩

theorem exact_original_graph : CoreTranslation.translate graph = .ok
    (.handle (.user 94 []) (.perform (.user 94 []) 0 (.integer 42))
      (.cons 0 1 10 (.resume 10 (.integer 42)) .nil)) := rfl

theorem original_root_source_authenticated : success rootCheck = true := by decide

theorem same_root_fixed_receiver_world_transport :
    ∃ source : IndexedSource (registry entries policy) [] owners [73] [] .none (environment [])
      (.handle (.user 94 []) (.perform (.user 94 []) 0 (.integer 42))
        (.cons 0 1 10 (.resume 10 (.integer 42)) .nil)) Contract.integer []
      ((RecursiveRequirements.Requirements.emitAfter (.request [] []) [] [⟨effect,0,false⟩]).prepend
        [.ordinary (.handler effect 0 declarations.table)])
      (.handler (effect := effect) (table := declarations.table) [] declarations.plans (.sequence .pure (.request (effect := effect) (operation := 0))))
      (Rows.handler declarations.rows (CoreCallableContractSource.sequenceRows Rows.pure Rows.request)),
      Authenticated (registry entries policy) [] source [] [] := by
  have valid := original_root_source_authenticated
  cases actual : rootCheck with
  | error error => simp [actual,success] at valid
  | ok receipt => exact receipt.world_weaken_current (by intro identity impossible; cases impossible)

private def formal : Template Contract.integer Contract.integer 10 [(1,Contract.integer)]
    (.resume 10 (.variable 1)) := .resume (.variable .head)
private def formalDeclarations (bound : List Nat) : Declarations entries effect Contract.integer []
    (.cons 0 1 10 (.resume 10 (.variable 1)) .nil) :=
  .cons .head formal bound (some []) (some []) [] [] .nil

theorem formal_receiver_checked :
    success (checkCurrentDeclarations (formalDeclarations [73]) policy [] owners [73] [] [] [73]) = true := by decide

theorem formal_receiver_not_hidden :
    (formalDeclarations []).currentBoundsCheck [] [73] = false := by decide

theorem unused_literal_support_not_erased :
    (formalDeclarations [73,74]).currentBoundsCheck [] [73] = false := by decide

theorem missing_clause_rejected : clauseKeysCheck entries effect .nil = false := by decide

theorem extra_clause_rejected : clauseKeysCheck entries effect
    (.cons 1 1 10 (.resume 10 (.integer 42)) .nil) = false := by decide

theorem duplicate_clause_rejected : clauseKeysCheck entries effect
    (.cons 0 1 10 (.resume 10 (.integer 42)) (.cons 0 1 10 (.resume 10 (.integer 42)) .nil)) = false := by decide

private def opaqueContract : Contract := .function .unit .integer [] [] (.choice .pure .pure) (Rows.choice Rows.pure Rows.pure)
theorem exact_full_binding : environment [(8,opaqueContract),(8,Contract.unit)] 8 = some opaqueContract := environment_first_binding

theorem older_full_binding_shadow_rejected :
    (BindingRef.tail (bound := 8) (value := Contract.unit) (BindingRef.head : BindingRef [(8,opaqueContract)] 8 opaqueContract)).check = false := by decide

theorem exact_full_operation : operations [(effect,0,opaqueContract,Contract.integer)] effect 0 = some (opaqueContract,Contract.integer) := by
  simp [operations]

theorem older_full_operation_shadow_rejected :
    (OperationRef.tail (requested := effect) (key := 0) (argument := Contract.unit) (answer := Contract.unit)
      (OperationRef.head : OperationRef [(effect,0,opaqueContract,Contract.integer)] effect 0 opaqueContract Contract.integer)).check = false := by decide

theorem formal_parameter_shadows_outer_support :
    (LexicalBounds.extend (LexicalBounds.extend [] 1 [74]) 1 [73]).environment 1 = [73] := rfl

#print axioms original_declaration_current_checked
#print axioms original_current_full_outputs
#print axioms exact_original_graph
#print axioms original_root_source_authenticated
#print axioms same_root_fixed_receiver_world_transport
#print axioms formal_receiver_checked
#print axioms formal_receiver_not_hidden
#print axioms unused_literal_support_not_erased
#print axioms missing_clause_rejected
#print axioms extra_clause_rejected
#print axioms duplicate_clause_rejected
#print axioms exact_full_binding
#print axioms older_full_binding_shadow_rejected
#print axioms exact_full_operation
#print axioms older_full_operation_shadow_rejected
#print axioms formal_parameter_shadows_outer_support
end Ash.OneShot.OriginalHandlerSeamProbes
