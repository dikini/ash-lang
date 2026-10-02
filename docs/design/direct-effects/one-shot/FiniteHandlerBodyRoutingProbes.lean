import CoreCallableFiniteHandlerBodyRoutes
namespace Ash.OneShot.FiniteHandlerBodyRoutingProbes
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract)
open CoreCallableStaticProducer CoreCallableFiniteClauseTemplate CoreCallableFiniteHandlerSource
open CoreCallableFiniteHandlerBodyRoutes
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open CoreCallableReceiverRefinement (LexicalBounds)
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
  CoreTranslation.Examples.node 4 (.integer 7) .integer,
  CoreTranslation.Examples.node 5 (.boolean true) .boolean,
  CoreTranslation.Examples.node 6 (.variable 20) .integer,
  CoreTranslation.Examples.node 7 (.bind ⟨20,.integer⟩ 1 5) .integer [.user 94 []],
  CoreTranslation.Examples.node 8 (.matchCases 4 [⟨.boolean true,6⟩,⟨.boolean false,1⟩]) .integer [.user 94 []],
  CoreTranslation.Examples.node 9 (.bind ⟨30,.integer⟩ 3 7) .integer [.user 94 []],
  {(originalGraph.nodes[3]'(by decide)) with kind := .handler 7 (.user 94 []) 8 [⟨0,.binder ⟨1,.integer⟩,4,2⟩]}],9⟩
private def clause : Template Contract.integer Contract.integer 45 [(1,Contract.integer)] (.resume 45 (.integer 42)) := .resume (.integer 42)
private def int (bindings : Bindings) (value : Int) : Annotation entries owners bindings (.integer value) Contract.integer [] (.request [] []) .pure Rows.pure := .integer value
private def bool (bindings : Bindings) : Annotation entries owners bindings (.boolean true) Contract.boolean [] (.request [] []) .pure Rows.pure := .boolean true
private def requestAnnotation (bindings : Bindings) := Annotation.perform reference (int bindings 42)
private def suffixAnnotation (bindings : Bindings) := Annotation.bind (parameter := 20) (requestAnnotation bindings)
  (Annotation.variable (BindingRef.head : BindingRef ((20,Contract.integer) :: bindings) 20 Contract.integer))
private def annotation := Annotation.bind (parameter := 30) (int [] 7)
  (Annotation.branch (bool [(30,Contract.integer)]) (suffixAnnotation [(30,Contract.integer)])
    (requestAnnotation [(30,Contract.integer)]) (.refl []))
private def route : Route entries owners effect 0 Contract.integer Contract.integer annotation :=
  .prefix (int [] 7) (.branch (bool [(30,Contract.integer)])
    (.suffix (.request reference (int [(30,Contract.integer)] 42))
      (.variable (BindingRef.head : BindingRef [(20,Contract.integer),(30,Contract.integer)] 20 Contract.integer)))
    (.request reference (int [(30,Contract.integer)] 42)) (.refl []))
private def rootCheck := CoreCallableFiniteHandlerBodyRoutes.check entries policy [] owners [] [] [] [] reference clause []
  (some []) (some []) [] [] annotation route [] [] [] []
private def success : Except CoreCallableFiniteHandlerAdmission.AdmissionError α → Bool
  | .ok _ => true
  | .error _ => false
private def expression : Code := .handle (.user 94 [])
  (.bind 30 (.integer 7) (.branch (.boolean true)
    (.bind 20 (.perform (.user 94 []) 0 (.integer 42)) (.variable 20)) (.perform (.user 94 []) 0 (.integer 42))))
  (.cons 0 1 45 (.resume 45 (.integer 42)) .nil)
private def initialCheck := CoreCallableFiniteHandlerBodyRoutes.checkInitial entries policy owners reference clause (some []) (some []) annotation route []

theorem literal_original_records : graph.nodes.take 3 = originalGraph.nodes.take 3 := rfl
 theorem original_handler_record : graph.nodes[9]'(by decide) =
    {(originalGraph.nodes[3]'(by decide)) with kind := .handler 7 (.user 94 []) 8 [⟨0,.binder ⟨1,.integer⟩,4,2⟩]} := rfl
 theorem literal_graph_shape : CoreSyntax.checkShape graph = .ok () := rfl
 theorem original_namespace_mapping : CoreTranslation.ticket originalGraph 4 = 10 ∧ CoreTranslation.ticket graph 4 = 45 := ⟨rfl,rfl⟩
 theorem original_graph_translation : CoreTranslation.translate graph = .ok expression := rfl
 theorem prefix_suffix_bool_checked : success rootCheck = true := by with_unfolding_all decide
 theorem actual_accounting_choice : route.root Front.nil clause =
    .choice (clauseRoot (Front.plain (.pure : RecipeTag SourceDeclarationPlans.Plan.pure) Rows.pure Front.nil) clause)
      (clauseRoot Front.nil clause) (.refl []) := by with_unfolding_all rfl

 theorem routed_result : Nonempty (Result entries policy [] owners [] [] [] [] reference clause []
    (some []) (some []) [] [] annotation route [] [] [] []) := by
  have checked := prefix_suffix_bool_checked
  cases actual : rootCheck with
  | error error => simp [actual,success] at checked
  | ok result => exact ⟨result⟩

 theorem protected_only_source_accepted :
    (match CoreCallableFiniteHandlerSource.check annotation
      (singleton reference clause [] none (some []) [] []) policy [] [] [] [] .none [] [] with
      | .ok _ => true | .error _ => false) = true := by decide
 theorem ordinary_unavailable_route_rejected :
    (match CoreCallableFiniteHandlerBodyRoutes.check entries policy [] owners [] [] [] [] reference clause []
      none (some []) [] [] annotation route [] [] [] [] with
      | .error .unavailableOrdinary => true | _ => false) = true := by with_unfolding_all decide

 theorem original_program_accepted : ∃ program, initialCheck = .ok program := by
  have sourceAccepted : ∃ result, rootCheck = .ok result := by
    have checked := prefix_suffix_bool_checked
    cases actual : rootCheck with
    | error error => simp [actual,success] at checked
    | ok result => exact ⟨result,rfl⟩
  obtain ⟨result,accepted⟩ := sourceAccepted
  simp only [rootCheck] at accepted
  have usage : CoreCallableCompositionalAdmissionFacets.usageCheck
      (.bind 30 (.integer 7) (.branch (.boolean true)
        (.bind 20 (.perform (.user 94 []) 0 (.integer 42)) (.variable 20))
        (.perform (.user 94 []) 0 (.integer 42)))) = true := rfl
  have support : CoreCallableGraphAnnotationChecks.subsetB
      (ScopedPorts.Support.evaluate ScopedPorts.Support.empty expression.dependencies) [] = true := rfl
  have evaluated : RecursiveRequirements.evaluate [] [] (OwnerPhaseTransitions.available [])
      (SourceScheduledCleanupInterfaces.Lexical.Recursive.annotateDisposals (route.root Front.nil clause)) = some ([] : Footprint) := by
    rw [actual_accounting_choice]
    simp [clause,clauseRoot,Front.root,quietRoot,
      SourceScheduledCleanupInterfaces.Lexical.Recursive.annotateDisposals,
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

 theorem original_initial_joint : ∃ program : CoreCallableInitialAdmission.Program
    ⟨operations entries,policy,owners⟩ (fun _ => none) [] expression,
    initialCheck = .ok program ∧ ScopedPortJoint.Valid
      (CoreCallableContractExecution.lowerOperations ⟨operations entries,policy,owners⟩).ports policy
      (fun _ => none) [] ⟨⟨⟨expression,.none,.nil⟩,[],[]⟩,[]⟩ program.result.port [] := by
  obtain ⟨program,accepted⟩ := original_program_accepted
  exact ⟨program,accepted,program.initial_joint⟩

private def doubleAnnotation := Annotation.bind (parameter := 20) (requestAnnotation [])
  (requestAnnotation [(20,Contract.integer)])
private def doubleRoute : Route entries owners effect 0 Contract.integer Contract.integer doubleAnnotation :=
  .suffix (.request reference (int [] 42)) (requestAnnotation [(20,Contract.integer)])
 theorem requested_suffix_source_accepted : (match CoreCallableFiniteHandlerSource.check doubleAnnotation
    (singleton reference clause [] (some []) (some []) [] []) policy [] [] [] [] .none [] [] with
    | .ok _ => true | .error _ => false) = true := by decide
 theorem requested_suffix_not_quiet : doubleRoute.valid = false := by with_unfolding_all rfl
 theorem requested_suffix_route_rejected : (match CoreCallableFiniteHandlerBodyRoutes.check entries policy [] owners [] [] [] []
    reference clause [] (some []) (some []) [] [] doubleAnnotation doubleRoute [] [] [] [] with
    | .error (.source (.unsupported "body route")) => true | _ => false) = true := by with_unfolding_all decide

private def opaqueContract : Contract := .function .unit .integer [] [] (.choice .pure .pure) (Rows.choice Rows.pure Rows.pure)
private def opaqueBody := Annotation.bind (parameter := 20) (requestAnnotation [(8,opaqueContract)])
  (Annotation.variable (BindingRef.tail BindingRef.head : BindingRef [(20,Contract.integer),(8,opaqueContract)] 8 opaqueContract))
private def opaqueRoute : Route entries owners effect 0 Contract.integer Contract.integer opaqueBody :=
  .suffix (.request reference (int [(8,opaqueContract)] 42))
    (.variable (BindingRef.tail BindingRef.head : BindingRef [(20,Contract.integer),(8,opaqueContract)] 8 opaqueContract))
private def opaqueClause : Template Contract.integer opaqueContract 45 [(1,Contract.integer),(8,opaqueContract)]
    (.resume 45 (.integer 42)) := .resume (.integer 42)
 theorem different_full_input_answer_checked : success (CoreCallableFiniteHandlerBodyRoutes.check entries policy [] owners [] [] [] [(8,opaqueContract)]
    reference opaqueClause [] (some []) (some []) [] [] opaqueBody opaqueRoute (LexicalBounds.extend [] 8 []) [] [] []) = true := by with_unfolding_all decide
 theorem full_opaque_private_indices : opaqueContract = .function .unit .integer [] []
    (.choice .pure .pure) (Rows.choice Rows.pure Rows.pure) := rfl

private def shadowBody := Annotation.bind (parameter := 20) (requestAnnotation [(20,opaqueContract)])
  (Annotation.variable (BindingRef.head : BindingRef [(20,Contract.integer),(20,opaqueContract)] 20 Contract.integer))
private def shadowRoute : Route entries owners effect 0 Contract.integer Contract.integer shadowBody :=
  .suffix (.request reference (int [(20,opaqueContract)] 42))
    (.variable (BindingRef.head : BindingRef [(20,Contract.integer),(20,opaqueContract)] 20 Contract.integer))
private def shadowClause : Template Contract.integer Contract.integer 45 [(1,Contract.integer),(20,opaqueContract)]
    (.resume 45 (.integer 42)) := .resume (.integer 42)
 theorem nearest_numeric_shadow_checked : success (CoreCallableFiniteHandlerBodyRoutes.check entries policy [] owners [] [] [] [(20,opaqueContract)]
    reference shadowClause [] (some []) (some []) [] [] shadowBody shadowRoute (LexicalBounds.extend [] 20 []) [] [] []) = true := by with_unfolding_all decide

private def skippedShadowBody := Annotation.bind (parameter := 20) (requestAnnotation [(20,opaqueContract)])
  (Annotation.variable (BindingRef.tail BindingRef.head : BindingRef [(20,Contract.integer),(20,opaqueContract)] 20 opaqueContract))
private def skippedShadowRoute : Route entries owners effect 0 Contract.integer Contract.integer skippedShadowBody :=
  .suffix (.request reference (int [(20,opaqueContract)] 42))
    (.variable (BindingRef.tail BindingRef.head : BindingRef [(20,Contract.integer),(20,opaqueContract)] 20 opaqueContract))
private def skippedShadowClause : Template Contract.integer opaqueContract 45 [(1,Contract.integer),(20,opaqueContract)]
    (.resume 45 (.integer 42)) := .resume (.integer 42)
 theorem skipped_numeric_shadow_rejected : (match CoreCallableFiniteHandlerBodyRoutes.check entries policy [] owners [] [] [] [(20,opaqueContract)]
    reference skippedShadowClause [] (some []) (some []) [] [] skippedShadowBody skippedShadowRoute (LexicalBounds.extend [] 20 []) [] [] [] with
    | .error (.source .lexicalShadowing) => true | _ => false) = true := by with_unfolding_all decide

private def uncheckedArm := Annotation.branch (bool []) (requestAnnotation []) doubleAnnotation (.refl [])
private def uncheckedArmRoute : Route entries owners effect 0 Contract.integer Contract.integer uncheckedArm :=
  .branch (bool []) (.request reference (int [] 42)) doubleRoute (.refl [])
 theorem literal_bool_does_not_skip_arm : uncheckedArmRoute.valid = false := by with_unfolding_all rfl
 theorem unchosen_requested_suffix_rejected : (match CoreCallableFiniteHandlerBodyRoutes.check entries policy [] owners [] [] [] []
    reference clause [] (some []) (some []) [] [] uncheckedArm uncheckedArmRoute [] [] [] [] with
    | .error (.source (.unsupported "body route")) => true | _ => false) = true := by with_unfolding_all decide

private def latentSlot : Contract := .function .unit .integer [] [⟨effect,0,false⟩]
  (.choice .pure .pure) (Rows.choice Rows.pure Rows.pure)
private def applyAnnotation := Annotation.app
  (Annotation.variable (BindingRef.tail BindingRef.head : BindingRef [(20,Contract.integer),(8,latentSlot)] 8 latentSlot))
  (Annotation.unit : Annotation entries owners [(20,Contract.integer),(8,latentSlot)] .unit .unit [] (.request [] []) .pure Rows.pure)
  (.choice .pure .pure)
private def applyBody := Annotation.bind (parameter := 20) (requestAnnotation [(8,latentSlot)]) applyAnnotation
private def applyRoute : Route entries owners effect 0 Contract.integer Contract.integer applyBody :=
  .suffix (.request reference (int [(8,latentSlot)] 42)) applyAnnotation
private def applyClause : Template Contract.integer Contract.integer 45 [(1,Contract.integer),(8,latentSlot)]
    (.resume 45 (.integer 42)) := .resume (.integer 42)
 theorem full_latent_quiet_application_checked : success (CoreCallableFiniteHandlerBodyRoutes.check entries policy [] owners [] [] [] [(8,latentSlot)]
    reference applyClause [] (some []) (some []) [] [] applyBody applyRoute (LexicalBounds.extend [] 8 []) [] [] []) = true := by with_unfolding_all decide
 theorem full_latent_slot_retained : latentSlot = .function .unit .integer [] [⟨effect,0,false⟩]
    (.choice .pure .pure) (Rows.choice Rows.pure Rows.pure) := rfl
 theorem nonempty_latent_private_recipe_quiet : [⟨effect,0,false⟩] ≠ ([] : Footprint) ∧
    CoreCallableCompositionalAdmissionFacets.quietCheck (CoreCallableCompositionalAdmissionFacets.annotationRecipe applyAnnotation) = true := by
  exact ⟨by decide,by with_unfolding_all rfl⟩

#print axioms literal_original_records
#print axioms original_handler_record
#print axioms literal_graph_shape
#print axioms original_namespace_mapping
#print axioms original_graph_translation
#print axioms prefix_suffix_bool_checked
#print axioms actual_accounting_choice
#print axioms routed_result
#print axioms protected_only_source_accepted
#print axioms ordinary_unavailable_route_rejected
#print axioms original_program_accepted
#print axioms original_initial_joint
#print axioms requested_suffix_source_accepted
#print axioms requested_suffix_not_quiet
#print axioms requested_suffix_route_rejected
#print axioms different_full_input_answer_checked
#print axioms full_opaque_private_indices
#print axioms nearest_numeric_shadow_checked
#print axioms skipped_numeric_shadow_rejected
#print axioms literal_bool_does_not_skip_arm
#print axioms unchosen_requested_suffix_rejected
#print axioms full_latent_quiet_application_checked
#print axioms full_latent_slot_retained
#print axioms nonempty_latent_private_recipe_quiet
end Ash.OneShot.FiniteHandlerBodyRoutingProbes
