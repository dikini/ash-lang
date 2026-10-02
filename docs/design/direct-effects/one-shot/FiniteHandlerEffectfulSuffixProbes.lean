import CoreCallableFiniteHandlerEffectfulSuffix
import FiniteHandlerBodyRoutingProbes
namespace Ash.OneShot.FiniteHandlerEffectfulSuffixProbes
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract)
open CoreCallableStaticProducer CoreCallableFiniteClauseTemplate CoreCallableFiniteHandlerSource
open CoreCallableFiniteHandlerBodyRoutes (Route Front annotationRows singleton)
open CoreCallableFiniteHandlerEffectfulSuffix
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open RecursiveRequirements (Requirements)
local instance : SourcePlannedChecks.DeclarationPolicy := SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
private def owners : CoreCallableContractRegistries.Owners := fun _ => none
private def policy : Syntax.TicketPolicy := fun _ => ⟨true,false⟩
private def effect : Instance := .user 94 []
private def entries : OperationEntries := [(effect,0,Contract.integer,Contract.integer)]
private def reference : OperationRef entries effect 0 Contract.integer Contract.integer := .head
private def originalGraph : CoreSyntax.Graph := ⟨[
  CoreTranslation.Examples.node 0 (.integer 42) .integer,
  CoreTranslation.Examples.node 1 (.request (.user 94 []) 0 0) .integer [.user 94 []],
  CoreTranslation.Examples.node 2 (.resume 7 4 .consumed 0) .integer,
  CoreTranslation.Examples.node 3 (.handler 7 (.user 94 []) 1 [⟨0,.binder ⟨1,.integer⟩,4,2⟩]) .integer],3⟩
private def graph : CoreSyntax.Graph := ⟨[
  originalGraph.nodes[0]'(by decide),originalGraph.nodes[1]'(by decide),originalGraph.nodes[2]'(by decide),
  CoreTranslation.Examples.node 4 (.variable 20) .integer,
  CoreTranslation.Examples.node 5 (.request (.user 94 []) 0 3) .integer [.user 94 []],
  CoreTranslation.Examples.node 6 (.bind ⟨20,.integer⟩ 1 4) .integer [.user 94 []],
  {(originalGraph.nodes[3]'(by decide)) with kind := .handler 7 (.user 94 []) 5 [⟨0,.binder ⟨1,.integer⟩,4,2⟩]}],6⟩
private def expression : Code := .handle (.user 94 [])
  (.bind 20 (.perform (.user 94 []) 0 (.integer 42)) (.perform (.user 94 []) 0 (.variable 20)))
  (.cons 0 1 32 (.resume 32 (.integer 42)) .nil)
private def clause : Template Contract.integer Contract.integer 32 [(1,Contract.integer)] (.resume 32 (.integer 42)) := .resume (.integer 42)
private def int (bindings : Bindings) : Annotation entries owners bindings (.integer 42) Contract.integer [] (.request [] []) .pure Rows.pure := .integer 42
private def second := Annotation.perform (owners := owners) reference
  (Annotation.variable (BindingRef.head : BindingRef [(20,Contract.integer)] 20 Contract.integer))
private def later : Route entries owners effect 0 Contract.integer Contract.integer second :=
  .request reference (.variable BindingRef.head)
private def annotation := Annotation.bind (parameter := 20) (Annotation.perform reference (int [])) second
private def route : SequentialRoute entries owners effect 0 Contract.integer Contract.integer annotation :=
  .sequence reference (int []) later
private def rootCheck := CoreCallableFiniteHandlerEffectfulSuffix.check entries policy [] owners [] [] [] [] reference clause []
  (some []) (some []) [] [] annotation route [] [] [] []
private def initialCheck := CoreCallableFiniteHandlerEffectfulSuffix.checkInitial entries policy owners reference clause (some []) (some []) annotation route []
private def success : Except CoreCallableFiniteHandlerAdmission.AdmissionError α → Bool
  | .ok _ => true
  | .error _ => false

theorem original_literal_prefix : graph.nodes.take 3 = originalGraph.nodes.take 3 := rfl
theorem original_handler_record : graph.nodes[6]'(by decide) =
  {(originalGraph.nodes[3]'(by decide)) with kind := .handler 7 (.user 94 []) 5 [⟨0,.binder ⟨1,.integer⟩,4,2⟩]} := rfl
theorem actual_graph_shape : CoreSyntax.checkShape graph = .ok () := rfl
theorem actual_owner_namespace : CoreTranslation.ticket graph 4 = 32 := rfl
theorem exact_original_translation : CoreTranslation.translate graph = .ok expression := rfl
theorem two_actual_requests_source_accepted : (match CoreCallableFiniteHandlerSource.check annotation
  (singleton reference clause [] (some []) (some []) [] []) policy [] [] [] [] .none [] [] with | .ok _ => true | _ => false) = true := by decide
theorem two_actual_requests_admitted : success rootCheck = true := by with_unfolding_all decide

theorem second_fresh_owner_distinct (first second : Nat)
    (absent : second ∉ (Context.spent (owner := first) Context.nil).ticketNames) : second ≠ first := by
  simpa [Context.ticketNames] using absent

theorem old_quiet_suffix_rejected :
  (Route.suffix (Route.request reference (int [])) second).valid = false := by with_unfolding_all rfl

theorem phase_sensitive_current_root : sequentialRoot route clause =
  .sequence (.request [] []) (.sequence (.request [] [])
    (.sequence (.request [] []) (.sequence (.request [] []) (.request [] [])))) := by with_unfolding_all rfl


theorem same_program_accepted : ∃ program, initialCheck = .ok program := by
  have sourceAccepted : ∃ result, rootCheck = .ok result := by
    have checked := two_actual_requests_admitted
    cases actual : rootCheck with
    | error error => simp [actual,success] at checked
    | ok result => exact ⟨result,rfl⟩
  obtain ⟨result,accepted⟩ := sourceAccepted
  simp only [rootCheck] at accepted
  have usage : CoreCallableCompositionalAdmissionFacets.usageCheck
    (.bind 20 (.perform (.user 94 []) 0 (.integer 42)) (.perform (.user 94 []) 0 (.variable 20))) = true := rfl
  have support : CoreCallableGraphAnnotationChecks.subsetB
    (ScopedPorts.Support.evaluate ScopedPorts.Support.empty expression.dependencies) [] = true := rfl
  have evaluated : RecursiveRequirements.evaluate [] [] (OwnerPhaseTransitions.available [])
    (SourceScheduledCleanupInterfaces.Lexical.Recursive.annotateDisposals (sequentialRoot route clause)) = some ([] : Footprint) := by
    rw [phase_sensitive_current_root]
    simp [SourceScheduledCleanupInterfaces.Lexical.Recursive.annotateDisposals,
      RecursiveRequirements.evaluate,RecursiveRequirements.evaluateFuel,ProtectionResiduals.merge,
      OwnerSource.exportAt,ProtectionResiduals.residualize,OwnerPhaseTransitions.project]
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

theorem same_initial_joint : ∃ program : CoreCallableInitialAdmission.Program
    ⟨operations entries,policy,owners⟩ (fun _ => none) [] expression,
    initialCheck = .ok program ∧ ScopedPortJoint.Valid
      (CoreCallableContractExecution.lowerOperations ⟨operations entries,policy,owners⟩).ports policy
      (fun _ => none) [] ⟨⟨⟨expression,.none,.nil⟩,[],[]⟩,[]⟩ program.result.port [] := by
  obtain ⟨program,accepted⟩ := same_program_accepted
  exact ⟨program,accepted,program.initial_joint⟩

theorem retained_source_requirements : annotation = Annotation.bind (parameter := 20)
    (Annotation.perform reference (int [])) second := rfl

theorem protected_only_source_accepted : (match CoreCallableFiniteHandlerSource.check annotation
  (singleton reference clause [] none (some []) [] []) policy [] [] [] [] .none [] [] with | .ok _ => true | _ => false) = true := by decide

theorem ordinary_unavailable_rejected : (match CoreCallableFiniteHandlerEffectfulSuffix.check entries policy [] owners [] [] [] [] reference clause []
  none (some []) [] [] annotation route [] [] [] [] with | .error .unavailableOrdinary => true | _ => false) = true := by with_unfolding_all decide

private def bool : Annotation entries owners [(20,Contract.integer)] (.boolean false) Contract.boolean [] (.request [] []) .pure Rows.pure := .boolean false
private def routedSecond := Annotation.branch bool second (int [(20,Contract.integer)]) (.refl [])
private def routedLater : Route entries owners effect 0 Contract.integer Contract.integer routedSecond :=
  .branch bool later (.quiet (int [(20,Contract.integer)])) (.refl [])
private def routedAnnotation := Annotation.bind (parameter := 20) (Annotation.perform reference (int [])) routedSecond
private def routed : SequentialRoute entries owners effect 0 Contract.integer Contract.integer routedAnnotation := .sequence reference (int []) routedLater

theorem later_bool_accounting_choice : sequentialRoot routed clause = .sequence (.request [] [])
  (.choice (routeRoot Front.nil (.sequence (.request [] []) (.request [] [])) clause later)
    (.sequence (.request [] []) (.request [] [])) (.refl [])) := by with_unfolding_all rfl

theorem both_later_routes_checked : success (CoreCallableFiniteHandlerEffectfulSuffix.check entries policy [] owners [] [] [] [] reference clause []
  (some []) (some []) [] [] routedAnnotation routed [] [] [] []) = true := by with_unfolding_all decide

private def badLater : Route entries owners effect 0 Contract.integer Contract.integer routedSecond :=
  .branch bool (.quiet second) (.quiet (int [(20,Contract.integer)])) (.refl [])
private def badRoute : SequentialRoute entries owners effect 0 Contract.integer Contract.integer routedAnnotation := .sequence reference (int []) badLater

theorem literal_condition_does_not_admit_unchecked_later : (match CoreCallableFiniteHandlerEffectfulSuffix.check entries policy [] owners [] [] [] [] reference clause []
  (some []) (some []) [] [] routedAnnotation badRoute [] [] [] [] with | .error (.source (.unsupported "body route")) => true | _ => false) = true := by with_unfolding_all decide

private def opaqueContract : Contract := .function .unit .integer [] [⟨effect,0,false⟩]
  (.choice .pure .pure) (Rows.choice Rows.pure Rows.pure)
private def opaqueSecond := Annotation.bind (parameter := 21)
  (Annotation.perform (owners := owners) reference
    (Annotation.variable (BindingRef.head : BindingRef [(20,Contract.integer),(8,opaqueContract)] 20 Contract.integer)))
  (Annotation.variable (BindingRef.tail (BindingRef.tail BindingRef.head) : BindingRef [(21,Contract.integer),(20,Contract.integer),(8,opaqueContract)] 8 opaqueContract))
private def opaqueLater : Route entries owners effect 0 Contract.integer Contract.integer opaqueSecond :=
  .suffix (.request reference (.variable BindingRef.head)) (.variable (BindingRef.tail (BindingRef.tail BindingRef.head)))
private def opaqueAnnotation := Annotation.bind (parameter := 20) (Annotation.perform reference (int [(8,opaqueContract)])) opaqueSecond
private def opaqueRoute : SequentialRoute entries owners effect 0 Contract.integer Contract.integer opaqueAnnotation := .sequence reference (int [(8,opaqueContract)]) opaqueLater
private def opaqueClause : Template Contract.integer opaqueContract 32 [(1,Contract.integer),(8,opaqueContract)] (.resume 32 (.integer 42)) := .resume (.integer 42)

theorem full_latent_private_family_answer_retained : opaqueContract = .function .unit .integer [] [⟨effect,0,false⟩]
  (.choice .pure .pure) (Rows.choice Rows.pure Rows.pure) := rfl

theorem operation_result_not_handler_answer_admitted : success (CoreCallableFiniteHandlerEffectfulSuffix.check entries policy [] owners [] [] [] [(8,opaqueContract)] reference opaqueClause []
  (some []) (some []) [] [] opaqueAnnotation opaqueRoute (CoreCallableReceiverRefinement.LexicalBounds.extend [] 8 []) [] [] []) = true := by with_unfolding_all decide


private def shadowSecond := Annotation.perform (owners := owners) reference
  (Annotation.variable (BindingRef.head : BindingRef [(20,Contract.integer),(20,opaqueContract)] 20 Contract.integer))
private def shadowLater : Route entries owners effect 0 Contract.integer Contract.integer shadowSecond := .request reference (.variable BindingRef.head)
private def shadowAnnotation := Annotation.bind (parameter := 20) (Annotation.perform reference (int [(20,opaqueContract)])) shadowSecond
private def shadowRoute : SequentialRoute entries owners effect 0 Contract.integer Contract.integer shadowAnnotation := .sequence reference (int [(20,opaqueContract)]) shadowLater
private def shadowClause : Template Contract.integer Contract.integer 32 [(1,Contract.integer),(20,opaqueContract)] (.resume 32 (.integer 42)) := .resume (.integer 42)

theorem nearest_body_shadow_preserves_outer_clause_slot : success (CoreCallableFiniteHandlerEffectfulSuffix.check entries policy [] owners [] [] [] [(20,opaqueContract)] reference shadowClause []
  (some []) (some []) [] [] shadowAnnotation shadowRoute (CoreCallableReceiverRefinement.LexicalBounds.extend [] 20 []) [] [] []) = true := by with_unfolding_all decide

private def skippedSecond := Annotation.bind (parameter := 21) shadowSecond
  (Annotation.variable (BindingRef.tail (BindingRef.tail BindingRef.head) : BindingRef [(21,Contract.integer),(20,Contract.integer),(20,opaqueContract)] 20 opaqueContract))
private def skippedLater : Route entries owners effect 0 Contract.integer Contract.integer skippedSecond :=
  .suffix shadowLater (.variable (BindingRef.tail (BindingRef.tail BindingRef.head)))
private def skippedAnnotation := Annotation.bind (parameter := 20) (Annotation.perform reference (int [(20,opaqueContract)])) skippedSecond
private def skippedRoute : SequentialRoute entries owners effect 0 Contract.integer Contract.integer skippedAnnotation := .sequence reference (int [(20,opaqueContract)]) skippedLater
private def skippedClause : Template Contract.integer opaqueContract 32 [(1,Contract.integer),(20,opaqueContract)] (.resume 32 (.integer 42)) := .resume (.integer 42)

theorem skipped_shadowed_full_slot_rejected : (match CoreCallableFiniteHandlerEffectfulSuffix.check entries policy [] owners [] [] [] [(20,opaqueContract)] reference skippedClause []
  (some []) (some []) [] [] skippedAnnotation skippedRoute (CoreCallableReceiverRefinement.LexicalBounds.extend [] 20 []) [] [] [] with | .error (.source .lexicalShadowing) => true | _ => false) = true := by with_unfolding_all decide

theorem same_effectful_body_rejected_by_old_checker : (match CoreCallableFiniteHandlerBodyRoutes.check entries policy [] owners [] [] [] [] reference clause []
    (some []) (some []) [] [] annotation (.suffix (.request reference (int [])) second) [] [] [] [] with
    | .error (.source (.unsupported "body route")) => true | _ => false) = true := by with_unfolding_all decide

#print axioms Ash.OneShot.FiniteHandlerEffectfulSuffixProbes.original_literal_prefix
#print axioms Ash.OneShot.FiniteHandlerEffectfulSuffixProbes.original_handler_record
#print axioms Ash.OneShot.FiniteHandlerEffectfulSuffixProbes.actual_graph_shape
#print axioms Ash.OneShot.FiniteHandlerEffectfulSuffixProbes.actual_owner_namespace
#print axioms Ash.OneShot.FiniteHandlerEffectfulSuffixProbes.exact_original_translation
#print axioms Ash.OneShot.FiniteHandlerEffectfulSuffixProbes.two_actual_requests_source_accepted
#print axioms Ash.OneShot.FiniteHandlerEffectfulSuffixProbes.two_actual_requests_admitted
#print axioms Ash.OneShot.FiniteHandlerEffectfulSuffixProbes.second_fresh_owner_distinct
#print axioms Ash.OneShot.FiniteHandlerEffectfulSuffixProbes.old_quiet_suffix_rejected
#print axioms Ash.OneShot.FiniteHandlerEffectfulSuffixProbes.phase_sensitive_current_root
#print axioms Ash.OneShot.FiniteHandlerEffectfulSuffixProbes.same_program_accepted
#print axioms Ash.OneShot.FiniteHandlerEffectfulSuffixProbes.same_initial_joint
#print axioms Ash.OneShot.FiniteHandlerEffectfulSuffixProbes.retained_source_requirements
#print axioms Ash.OneShot.FiniteHandlerEffectfulSuffixProbes.protected_only_source_accepted
#print axioms Ash.OneShot.FiniteHandlerEffectfulSuffixProbes.ordinary_unavailable_rejected
#print axioms Ash.OneShot.FiniteHandlerEffectfulSuffixProbes.later_bool_accounting_choice
#print axioms Ash.OneShot.FiniteHandlerEffectfulSuffixProbes.both_later_routes_checked
#print axioms Ash.OneShot.FiniteHandlerEffectfulSuffixProbes.literal_condition_does_not_admit_unchecked_later
#print axioms Ash.OneShot.FiniteHandlerEffectfulSuffixProbes.full_latent_private_family_answer_retained
#print axioms Ash.OneShot.FiniteHandlerEffectfulSuffixProbes.operation_result_not_handler_answer_admitted
#print axioms Ash.OneShot.FiniteHandlerEffectfulSuffixProbes.nearest_body_shadow_preserves_outer_clause_slot
#print axioms Ash.OneShot.FiniteHandlerEffectfulSuffixProbes.skipped_shadowed_full_slot_rejected
#print axioms Ash.OneShot.FiniteHandlerEffectfulSuffixProbes.same_effectful_body_rejected_by_old_checker
end Ash.OneShot.FiniteHandlerEffectfulSuffixProbes
