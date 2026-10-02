import CoreCallableFiniteHandlerAdmission
namespace Ash.OneShot.FiniteHandlerAdmissionProbes
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract)
open CoreCallableStaticProducer CoreCallableFiniteClauseTemplate CoreCallableFiniteHandlerSource
open CoreCallableFiniteHandlerAdmission
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open CoreCallableReceiverRefinement (LexicalBounds)
open RecursiveRequirements (Requirements)
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy
private def owners : CoreCallableContractRegistries.Owners := fun _ => none
private def policy : Syntax.TicketPolicy := fun _ => ⟨true,false⟩
private def effect : Instance := .user 94 []
private def entries : OperationEntries := [(effect,0,Contract.integer,Contract.integer)]
private def clause : Template Contract.integer Contract.integer 10 [(1,Contract.integer)] (.resume 10 (.integer 42)) :=
  .resume (.integer 42)
private def operand : Annotation entries owners [] (.integer 42) Contract.integer [] (.request [] []) .pure Rows.pure := .integer 42
private def rootCheck := CoreCallableFiniteHandlerAdmission.check entries policy [] owners [] [] [] []
  .head clause [] (some []) (some []) [] [] operand [] [] [] []
private def success : Except AdmissionError α → Bool
  | .ok _ => true
  | .error _ => false

theorem original_request_contextual_checked : success rootCheck = true := by decide

theorem same_root_result : Nonempty (Result entries policy [] owners [] [] [] []
    (OperationRef.head : OperationRef entries effect 0 Contract.integer Contract.integer) clause [] (some []) (some []) [] [] operand [] [] [] []) := by
  have checked := original_request_contextual_checked
  cases actual : rootCheck with
  | error error => simp [actual,success] at checked
  | ok receipt => exact ⟨receipt⟩

private def graph : CoreSyntax.Graph := ⟨[
  CoreTranslation.Examples.node 0 (.integer 42) .integer,
  CoreTranslation.Examples.node 1 (.request (.user 94 []) 0 0) .integer [.user 94 []],
  CoreTranslation.Examples.node 2 (.resume 7 4 .consumed 0) .integer,
  CoreTranslation.Examples.node 3 (.handler 7 (.user 94 []) 1 [⟨0,.binder ⟨1,.integer⟩,4,2⟩]) .integer],3⟩

theorem same_four_node_translation : CoreTranslation.translate graph = .ok
    (.handle (.user 94 []) (.perform (.user 94 []) 0 (.integer 42))
      (.cons 0 1 10 (.resume 10 (.integer 42)) .nil)) := rfl

theorem ordinary_unavailable_source_accepted :
    (match CoreCallableFiniteHandlerSource.check (.perform .head operand)
      (single (OperationRef.head : OperationRef entries effect 0 Contract.integer Contract.integer) clause [] none (some []) [] [])
      policy [] [] [] [] .none [] [] with | .ok _ => true | .error _ => false) = true := by decide

theorem ordinary_unavailable_contextual_rejected :
    (match CoreCallableFiniteHandlerAdmission.check entries policy [] owners [] [] [] []
      .head clause [] none (some []) [] [] operand [] [] [] [] with
      | .error .unavailableOrdinary => true | _ => false) = true := by decide

private def composed : Template Contract.integer Contract.integer 10 [(1,Contract.integer)]
    (.branch (.boolean true) (.resume 10 (.integer 42))
      (.bind 3 (.integer 7) (.resume 10 (.variable 1)))) :=
  .branch (.boolean true) (.resume (.integer 42)) (.bind (.integer 7) (.resume (.variable (.tail .head))))

theorem finite_prefix_branch_checked :
    success (CoreCallableFiniteHandlerAdmission.check entries policy [] owners [] [] [] []
      .head composed [] (some []) (some []) [] [] operand [] [] [] []) = true := by decide

theorem branch_accounting_keeps_choice : outerRoot composed =
    .choice (outerRoot clause) (outerRoot clause) (.refl []) := rfl

theorem private_owner_zero_one_distinct : composed.dependencies 0 ≠ composed.dependencies 1 := by
  simp [composed,Template.dependencies]

theorem local_owner_balance : RecursiveRequirements.LocalOwner owner .available (localRoot owner composed) (outerRoot composed) .consumed :=
  retire_local composed rfl

private def opaqueContract : Contract := .function .unit .integer [] [] (.choice .pure .pure) (Rows.choice Rows.pure Rows.pure)
private def opaqueEntries : OperationEntries := [(effect,0,opaqueContract,opaqueContract)]
private def opaqueClause : Template opaqueContract opaqueContract 10 [(1,opaqueContract),(8,opaqueContract)] (.resume 10 (.variable 1)) := .resume (.variable .head)
private def opaqueOperand : Annotation opaqueEntries owners [(8,opaqueContract)] (.variable 8) opaqueContract [] (.request [] []) .pure Rows.pure := .variable .head

theorem full_opaque_contract_checked : success (CoreCallableFiniteHandlerAdmission.check opaqueEntries policy [] owners [] [] [] [(8,opaqueContract)]
    .head opaqueClause [] (some []) (some []) [] [] opaqueOperand (LexicalBounds.extend [] 8 []) [] [] []) = true := by decide

theorem opaque_original_indices_retained : opaqueContract =
    .function .unit .integer [] [] (.choice .pure .pure) (Rows.choice Rows.pure Rows.pure) := rfl

#print axioms original_request_contextual_checked
#print axioms same_root_result
#print axioms same_four_node_translation
#print axioms ordinary_unavailable_source_accepted
#print axioms ordinary_unavailable_contextual_rejected
#print axioms finite_prefix_branch_checked
#print axioms branch_accounting_keeps_choice
#print axioms private_owner_zero_one_distinct
#print axioms local_owner_balance
#print axioms full_opaque_contract_checked
#print axioms opaque_original_indices_retained


private def expression : Code := .handle (.user 94 []) (.perform (.user 94 []) 0 (.integer 42))
    (.cons 0 1 10 (.resume 10 (.integer 42)) .nil)
private def initialCheck := checkInitial entries policy owners
    (OperationRef.head : OperationRef entries effect 0 Contract.integer Contract.integer) clause (some []) (some []) operand []

theorem same_root_program_accepted : ∃ program, initialCheck = .ok program := by
  have sourceAccepted : ∃ result, rootCheck = .ok result := by
    have checked := original_request_contextual_checked
    cases actual : rootCheck with
    | error error => simp [actual,success] at checked
    | ok result => exact ⟨result,rfl⟩
  obtain ⟨result,accepted⟩ := sourceAccepted
  simp only [rootCheck] at accepted
  have usage : CoreCallableCompositionalAdmissionFacets.usageCheck (.integer 42) = true := rfl
  have support : CoreCallableGraphAnnotationChecks.subsetB
      (ScopedPorts.Support.evaluate ScopedPorts.Support.empty expression.dependencies) [] = true := rfl
  have evaluated : RecursiveRequirements.evaluate [] [] (OwnerPhaseTransitions.available [])
      (SourceScheduledCleanupInterfaces.Lexical.Recursive.annotateDisposals (outerRoot clause)) = some ([] : Footprint) := by
    simp [clause,outerRoot, SourceScheduledCleanupInterfaces.Lexical.Recursive.annotateDisposals,
      RecursiveRequirements.evaluate, RecursiveRequirements.evaluateFuel, ProtectionResiduals.merge,
      OwnerSource.exportAt, ProtectionResiduals.residualize, OwnerPhaseTransitions.project]
  unfold initialCheck checkInitial
  rw [accepted]
  dsimp only
  split
  next h =>
    split
    next h =>
      split
      next h =>
        split
        next h =>
          split
          next absent => simp [evaluated] at absent
          next row found =>
            have rowEq : row = [] := Option.some.inj (found.symm.trans evaluated)
            subst row
            split
            next bounded => exact ⟨_,rfl⟩
            next refused => exact False.elim (refused rfl)
        next refused => exact False.elim (refused support)
      next refused => exact False.elim (refused rfl)
    next refused => exact False.elim (refused rfl)
  next refused => exact False.elim (refused usage)

theorem same_root_program_checked : success initialCheck = true := by
  obtain ⟨program,accepted⟩ := same_root_program_accepted
  simp [accepted,success]

theorem same_root_program : Nonempty (CoreCallableInitialAdmission.Program
    ⟨operations entries,policy,owners⟩ (fun _ => none) [] expression) := by
  obtain ⟨program,_⟩ := same_root_program_accepted
  exact ⟨program⟩

theorem same_root_initial_joint : ∃ result,
    ScopedPortJoint.Valid (CoreCallableContractExecution.lowerOperations ⟨operations entries,policy,owners⟩).ports
      policy (fun _ => none) [] ⟨⟨⟨expression,.none,.nil⟩,[],[]⟩,[]⟩ result [] := by
  obtain ⟨program⟩ := same_root_program
  exact ⟨program.result.port,program.initial_joint⟩

theorem same_graph_program_code : CoreTranslation.translate graph = .ok expression := rfl

theorem source_accounting_roots_distinct :
    (RecursiveRequirements.Requirements.prepend [.ordinary (.handler effect 0
      (single (OperationRef.head : OperationRef entries effect 0 Contract.integer Contract.integer) clause [] (some []) (some []) [] []).table)]
      (.emitAfter (.request [] []) [] [⟨effect,0,false⟩])) ≠ outerRoot clause := by
  intro same
  cases same

#print axioms same_root_program_accepted
#print axioms same_root_program_checked
#print axioms same_root_program
#print axioms same_root_initial_joint
#print axioms same_graph_program_code
#print axioms source_accounting_roots_distinct
end Ash.OneShot.FiniteHandlerAdmissionProbes
