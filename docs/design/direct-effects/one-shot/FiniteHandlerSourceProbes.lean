import CoreCallableFiniteHandlerSource
namespace Ash.OneShot.FiniteHandlerSourceProbes
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract)
open CoreCallableStaticProducer CoreCallableFiniteClauseTemplate CoreCallableFiniteHandlerSource
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open CoreCallableReceiverRefinement (LexicalBounds)
open SourceDeclarationPlans (Plan ModePlans)
open SourceDependencyAnnotations (Dependencies)

private def owners : CoreCallableContractRegistries.Owners := fun _ => none
private def policy : Syntax.TicketPolicy := fun _ => ⟨true,false⟩
private def denied : Syntax.TicketPolicy := fun _ => ⟨false,false⟩
private def clause : Template Contract.integer Contract.integer 2 [(1,Contract.integer)] (.resume 2 (.integer 42)) :=
  .resume (.integer 42)
private def success : Except Error α → Bool
  | .ok _ => true
  | .error _ => false

theorem owner_distinction : clause.dependencies 0 ≠ clause.dependencies 1 := by
  simp [clause,Template.dependencies]

theorem ordinary_offer_checked :
    success (checkOffer clause [] policy [] owners [] [] [] [] false false []
      (LexicalBounds.extend [] 1 []) []) = true := by decide

theorem protected_offer_checked :
    success (checkOffer clause [] policy [] owners [] [] [] [] true false []
      (LexicalBounds.extend [] 1 []) []) = true := by decide

theorem denied_resume_rejected :
    success (checkOffer clause [] denied [] owners [] [] [] [] false false []
      (LexicalBounds.extend [] 1 []) []) = false := by decide

private def opaqueContract : Contract := .function .unit .integer [] [] (.choice .pure .pure) (Rows.choice Rows.pure Rows.pure)
private def fullSlot : Pure [(8,opaqueContract)] (.variable 8) opaqueContract := .variable .head

theorem whole_higher_order_slot_checked :
    success (fullSlot.check [] policy [] [] [] (LexicalBounds.extend [] 8 []) []) = true := by decide

private def shadowed : Pure [(8,Contract.unit),(8,opaqueContract)] (.variable 8) opaqueContract := .variable (.tail .head)
theorem shadowed_full_slot_rejected :
    success (shadowed.check [] policy [] [] [] (LexicalBounds.extend [] 8 []) []) = false := by decide

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

theorem actual_request_handler_checked : success rootCheck = true := by decide

theorem same_handler_source_auth : Nonempty (HandlerReceipt entries policy [] owners [] [] [] .none []
    (.perform (.user 94 []) 0 (.integer 42)) Contract.integer []
    (.emitAfter (.request [] []) [] [⟨effect,0,false⟩]) (.sequence .pure (.request (effect := effect) (operation := 0)))
    (CoreCallableContractSource.sequenceRows Rows.pure Rows.request) declarations [] []) := by
  have checked := actual_request_handler_checked
  cases actual : rootCheck with
  | error error => simp [actual,success] at checked
  | ok receipt => exact ⟨receipt⟩

private def graph : CoreSyntax.Graph := ⟨[
  CoreTranslation.Examples.node 0 (.integer 42) .integer,
  CoreTranslation.Examples.node 1 (.request (.user 94 []) 0 0) .integer [.user 94 []],
  CoreTranslation.Examples.node 2 (.resume 7 4 .consumed 0) .integer,
  CoreTranslation.Examples.node 3 (.handler 7 (.user 94 []) 1 [⟨0,.binder ⟨1,.integer⟩,4,2⟩]) .integer],3⟩

theorem actual_closed_graph_translation : CoreTranslation.translate graph = .ok
    (.handle (.user 94 []) (.perform (.user 94 []) 0 (.integer 42))
      (.cons 0 1 10 (.resume 10 (.integer 42)) .nil)) := rfl

theorem root_ordinary_dependencies_closed :
    (Code.handle (.user 94 []) (.perform (.user 94 []) 0 (.integer 42))
      (.cons 0 1 10 (.resume 10 (.integer 42)) .nil)).dependencies = [] := rfl

private def literalAvailable : Code := .integer 42
private def literalDouble : Code := .bind 3 (.resume 10 (.integer 42)) (.resume 10 (.integer 42))
private def literalEscape : Code := .lambda 3 (.resume 10 (.integer 42))

theorem actual_left_available_state : currentUse policy (.ticket 10 (policy 10)) .available literalAvailable = some .available := rfl
theorem actual_double_use_rejected : currentUse policy (.ticket 10 (policy 10)) .available literalDouble = none := rfl
theorem actual_escape_rejected : currentUse policy (.ticket 10 (policy 10)) .available literalEscape = none := rfl

theorem literal_left_available_no_use : ¬ Uses policy (.ticket 10 (policy 10)) .available literalAvailable .consumed := by
  intro impossible; cases impossible
 theorem literal_double_no_use : ¬ Uses policy (.ticket 10 (policy 10)) .available literalDouble .consumed := by
  intro impossible
  cases impossible with
  | bind first second =>
    cases first with
    | resume permission operand =>
      cases operand
      cases second with
      | resume permission operand => cases operand
 theorem literal_escape_no_use : ¬ Uses policy (.ticket 10 (policy 10)) .available literalEscape .consumed := by
  intro impossible
  cases impossible

theorem missing_operation_rejected : clauseKeysCheck entries effect .nil = false := by decide
 theorem duplicate_operation_rejected : clauseKeysCheck entries effect
    (.cons 0 1 10 (.resume 10 (.integer 42)) (.cons 0 2 11 (.resume 11 (.integer 42)) .nil)) = false := by decide
 theorem extra_operation_rejected : clauseKeysCheck entries effect
    (.cons 0 1 10 (.resume 10 (.integer 42)) (.cons 1 2 11 (.resume 11 (.integer 42)) .nil)) = false := by decide

private def protectedOnly : Declarations entries effect Contract.integer []
    (.cons 0 1 10 (.resume 10 (.integer 42)) .nil) := .cons .head rootClause [] none (some []) [] [] .nil

theorem unavailable_ordinary_remains_none : (ProtectionContracts.lookup 0 protectedOnly.table).map
    ProtectionContracts.ClauseContract.unprotectedRow = some none := rfl
 theorem selected_protected_exact : (ProtectionContracts.lookup 0 protectedOnly.table).map
    ProtectionContracts.ClauseContract.protectedRow = some (some []) := rfl
 theorem protected_only_handler_checked : success
    (CoreCallableFiniteHandlerSource.check rootAnnotation protectedOnly policy [] [] [] [] .none [] []) = true := by decide

private def branchClause : Template Contract.integer Contract.integer 10 [(1,Contract.integer)]
    (.bind 5 (.integer 1) (.branch (.boolean true) (.resume 10 (.variable 5)) (.resume 10 (.integer 42)))) :=
  .bind (.integer 1) (.branch (.boolean true) (.resume (.variable .head)) (.resume (.integer 42)))
 theorem composed_prefix_branch_checked : success
    (checkOffer branchClause entries policy [] owners [] [] [] [] false false [] (LexicalBounds.extend [] 1 []) []) = true := by decide

theorem actual_graph_shape : CoreSyntax.checkShape graph = .ok () := rfl

private def badDeclarations (body : Template Contract.integer Contract.integer 10 [(1,Contract.integer)] code) :
    Declarations entries effect Contract.integer [] (.cons 0 1 10 code .nil) :=
  .cons .head body [] (some []) (some []) [] [] .nil
 theorem actual_available_clause_rejected : checkDeclarations
    (badDeclarations (Template.unsupported "literal available" : Template Contract.integer Contract.integer 10 [(1,Contract.integer)] literalAvailable))
    policy [] owners [] [] [] [] = .error .capability := rfl
 theorem actual_double_clause_rejected : checkDeclarations
    (badDeclarations (Template.unsupported "literal double" : Template Contract.integer Contract.integer 10 [(1,Contract.integer)] literalDouble))
    policy [] owners [] [] [] [] = .error .capability := rfl
 theorem actual_escape_clause_rejected : checkDeclarations
    (badDeclarations (Template.unsupported "literal escape" : Template Contract.integer Contract.integer 10 [(1,Contract.integer)] literalEscape))
    policy [] owners [] [] [] [] = .error .capability := rfl

private def higherClause : Template opaqueContract opaqueContract 10 [(1,Contract.unit),(8,opaqueContract)] (.resume 10 (.variable 8)) :=
  .resume (.variable (.tail .head))
 theorem full_higher_order_clause_checked : success
    (checkOffer higherClause entries policy [] owners [] [] [] [] false false []
      (LexicalBounds.extend (LexicalBounds.extend [] 8 []) 1 []) []) = true := by decide
 theorem unavailable_mode_exact : modePlan rootClause none = ModePlans.unavailable := rfl
 theorem protected_full_family_exact : modePlan rootClause (some []) = ModePlans.available rootClause.plan := rfl

#print axioms owner_distinction
#print axioms ordinary_offer_checked
#print axioms protected_offer_checked
#print axioms denied_resume_rejected
#print axioms whole_higher_order_slot_checked
#print axioms shadowed_full_slot_rejected
#print axioms actual_request_handler_checked
#print axioms same_handler_source_auth
#print axioms actual_closed_graph_translation
#print axioms root_ordinary_dependencies_closed
#print axioms actual_left_available_state
#print axioms actual_double_use_rejected
#print axioms actual_escape_rejected
#print axioms literal_left_available_no_use
#print axioms literal_double_no_use
#print axioms literal_escape_no_use
#print axioms missing_operation_rejected
#print axioms duplicate_operation_rejected
#print axioms extra_operation_rejected
#print axioms unavailable_ordinary_remains_none
#print axioms selected_protected_exact
#print axioms protected_only_handler_checked
#print axioms composed_prefix_branch_checked
#print axioms actual_graph_shape
#print axioms actual_available_clause_rejected
#print axioms actual_double_clause_rejected
#print axioms actual_escape_clause_rejected
#print axioms full_higher_order_clause_checked
#print axioms unavailable_mode_exact
#print axioms protected_full_family_exact
end Ash.OneShot.FiniteHandlerSourceProbes
