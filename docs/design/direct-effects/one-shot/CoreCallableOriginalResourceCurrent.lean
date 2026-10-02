import CompositionalInitialAdmissionProbes
import ComposedResourceRuntimeOriginProbes
import CoreCallableRichBetaCore
namespace Ash.OneShot.CoreCallableOriginalResourceCurrent
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract Environment)
open CoreCallableContractAdmission CoreCallableReceiverRefinement CoreCallableContractExecution
open CoreCallableCompositionalAdmissionFacets CoreCallableCompositionalResourceOpening
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
local instance : SourcePlannedChecks.DeclarationPolicy := declarationPolicy
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace Original
abbrev graph := CoreCallableCompositionalResourceRoot.graph
abbrev globals := CoreCallableCompositionalResourceRoot.globals
abbrev body := CoreCallableCompositionalResourceRoot.body
abbrev checking := CoreCallableCompositionalResourceRoot.checkingOf body
abbrev needs := CoreCallableCompositionalResourceRoot.needsOf body
abbrev selection := ComposedResourceRuntimeOriginProbes.selection
abbrev bodyCode := CoreCallableCompositionalResourceRoot.codeOf body
abbrev openedCode := bodyCode.instantiate (Instantiation.Environment.empty.bind 3 0)
abbrev outerClosedCode := openedCode.subst 7 (.integer 17)
abbrev cellStack : Stack := .push (.cell 0 0 .none .integer) .nil
abbrev cellContext := Context.cell (identity := 0) Context.nil
abbrev root := (rootAccount CoreCallableCompositionalResourceRoot.initializerAnnotation body).requirements

/-- Quietness comes from the executed initializer recipe; it is not a value. -/
theorem initializer_quiet : quietCheck
    (annotationRecipe CoreCallableCompositionalResourceRoot.initializerAnnotation) = true := by decide +kernel

theorem initializer_account : rootAccount CoreCallableCompositionalResourceRoot.initializerAnnotation body =
    checkingAccount checking .done := by decide +kernel

theorem opening : Opening CoreCallableFiniteCellRegistry.original
    CoreCallableCompositionalResourceRoot.entries CoreCallableCompositionalResourceRoot.policy []
    globals.owners [] [] .none CoreCallableCompositionalResourceRoot.original 3 body [(7,[])] [] := check_opening (entries := CoreCallableCompositionalResourceRoot.entries)
  (policy := CoreCallableCompositionalResourceRoot.policy) (outward := [])
  (owners := globals.owners) (scope := .none) body
  (show openingCheck CoreCallableCompositionalResourceRoot.original body
    CoreCallableFiniteCellRegistry.original 3 [] [] [(7,[])] [] = true from rfl)

theorem lexical_empty : CoreCallableReceiverRefinement.LexicalBounds.environment [(7,[])] =
    ScopedPorts.Support.empty := by
  funext name
  by_cases same : name = 7 <;>
    simp [CoreCallableReceiverRefinement.LexicalBounds.environment,
      CoreCallableReceiverRefinement.LexicalBounds.lookup,ScopedPorts.Support.empty,same]

/-- Actual allocation0 selects the original all-fresh Source/Auth output. -/
theorem supported : CoreCallableContractAdmission.Supported globals [] [0] [.cell 0] .none
    (Environment.empty.extend 7 .integer)
    (ScopedPorts.Support.extend ScopedPorts.Support.empty 7 [])
    openedCode .integer [] (needs.requirements 0) (checking.plan 0) (checking.rows 0) [0] [0] := by
  let source := opening.source 0 (by simp)
  have auth := opening.auth 0 (by simp)
  have env : ScopedPorts.Support.extend ScopedPorts.Support.empty 7 [] = ScopedPorts.Support.empty := by
    funext name; simp [ScopedPorts.Support.extend,ScopedPorts.Support.empty]
  refine ⟨source,?_,List.Subset.refl _,⟨[(7,[])],?_,auth⟩,List.Subset.refl _⟩
  · rw [env,← lexical_empty]; exact auth.current_support
  · rw [env]; exact lexical_empty

def integerCheck := CoreCallableFiniteRegistryBridge.recheck
  (CoreCallableStaticProducer.Annotation.integer 17 :
    CoreCallableStaticProducer.Annotation CoreCallableCompositionalResourceRoot.entries globals.owners []
      (.integer 17) .integer [] (.request [] []) .pure Rows.pure)
  CoreCallableFiniteCellRegistry.original CoreCallableCompositionalResourceRoot.policy [] [0] [.cell 0] .none [] [0]

theorem integer_checked : ∃ receipt, integerCheck = .ok receipt := ⟨_,rfl⟩
theorem integerSupported : CoreCallableContractAdmission.Supported globals [] [0] [.cell 0] .none
    Environment.empty ScopedPorts.Support.empty (.integer 17) .integer [] (.request [] []) .pure Rows.pure [] [0] := by
  obtain ⟨receipt,accepted⟩ := integer_checked
  obtain ⟨source,_tree,auth,_⟩ := CoreCallableFiniteRegistryBridge.recheck_success accepted
  exact ⟨source,SourceSupport.bounds_iff.mpr (by simp [Code.dependencies,ScopedPorts.Support.evaluate]),by simp,
    ⟨[],rfl,auth⟩,List.Subset.refl _⟩

theorem closed_source : ∃ nextPlan : Plan _, ∃ nextRows : Rows (signature nextPlan),
    CoreCallableContractAdmission.Supported globals [] [0] [.cell 0] .none Environment.empty ScopedPorts.Support.empty
      outerClosedCode .integer [] (needs.requirements 0) nextPlan nextRows [0] [0] ∧
    nextPlan = CoreCallablePlanSubstitution.plan openedCode (checking.plan 0) 7 (.integer 17) ∧
    signature nextPlan = signature (checking.plan 0) ∧ HEq nextRows (checking.rows 0) :=
  supported.substitution integerSupported (by simp [ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Code.dependencies])

private theorem transport_rows
    {first second : SourcePlanSignatures.Signature dependencies}
    {firstRows : Rows first} {secondRows : Rows second}
    (same : first = second) (sameRows : HEq firstRows secondRows)
    (certificate : SourceAdmission.Code [] (fun _ => none) [] (OwnerPhaseTransitions.available [])
      [0] [] secondRows cellContext)
    (checked : InstallationSupport.CodeChecked [] [] certificate)
    (run : Accounting.Run [0] [] secondRows cellContext root) :
    ∃ nextCertificate : SourceAdmission.Code [] (fun _ => none) [] (OwnerPhaseTransitions.available [])
      [0] [] firstRows cellContext,
      InstallationSupport.CodeChecked [] [] nextCertificate ∧ Accounting.Run [0] [] firstRows cellContext root := by
  subst second
  cases eq_of_heq sameRows
  exact ⟨certificate,checked,run⟩

/-- Exact private rows and the original root survive outer7 substitution. -/
theorem opened_site : ∃ site : Site globals [] [0] [.cell 0] (fun _ => none)
    (OwnerPhaseTransitions.available []) [] [] [] outerClosedCode .none cellStack
    .integer .integer cellContext root,
    HEq site.plan (CoreCallablePlanSubstitution.plan openedCode (checking.plan 0) 7 (.integer 17)) ∧
    HEq site.rows (checking.rows 0) := by
  obtain ⟨plan,rows,current,exactPlan,sameSignature,sameRows⟩ := closed_source
  let facets := fresh_facets (outward := []) (actions := fun _ => none) (budget := [])
    (phases := OwnerPhaseTransitions.available []) (world := []) (installations := []) (ambient := [])
    checking (binder := 3) (by rfl) 0
  have run : Accounting.Run [0] [] (checking.rows 0) cellContext root := by
    simpa only [root,initializer_account,List.nil_append] using facets.accounting
  obtain ⟨certificate,checked,accounting⟩ := transport_rows sameSignature sameRows facets.certificate facets.checked run
  have evaluated : RecursiveRequirements.evaluate [] [] (OwnerPhaseTransitions.available [])
      (annotateDisposals root) = some ([] : Footprint) := by
    have accountEq : rootAccount CoreCallableCompositionalResourceRoot.initializerAnnotation body = .choice .done .done := by decide +kernel
    simp [root,accountEq,Account.requirements,annotateDisposals,RecursiveRequirements.evaluate,
      RecursiveRequirements.evaluateFuel,ProtectionResiduals.merge,OwnerSource.exportAt,ProtectionResiduals.residualize,
      OwnerPhaseTransitions.project]
  let site : Site globals [] [0] [.cell 0] (fun _ => none) (OwnerPhaseTransitions.available []) [] [] []
      outerClosedCode .none cellStack .integer .integer cellContext root :=
    { sourceDemand := [],requirements := needs.requirements 0,dependencies := _,plan := plan,rows := rows,
      bound := [0],current := by simpa [actualReceiver,SourceDependencyCapture.Scope.visibleResources] using current,
      received := by simp [SourceDependencyCapture.Scope.visibleResources],
      certificate := certificate,certificateChecked := checked,
      pending := .cell (by simp) rfl .nil,retained := .cell .nil,retainedChecked := .cell .nil,
      accounting := accounting,annotated := root,annotation := .original,row := [],
      checked := RecursiveRequirements.evaluate_sound evaluated,bounded := List.Subset.refl _ }
  exact ⟨site,heq_of_eq exactPlan,sameRows⟩

abbrev handleTail : Code := match outerClosedCode with | .bind _ _ tail => tail | _ => .unit

theorem handle_shape : outerClosedCode = .bind 9 (.resourceRef (.activation 0)) handleTail := rfl

theorem handle_closed : ClosedExcept 9 handleTail := by
  intro name member
  change Syntax.Dependency.variable name ∈ [.resource 0,.variable 9] at member
  simpa using member

theorem p9_code : handleTail.subst 9 (.resourceRef (.activation 0)) = selection.p9.target.expression := rfl

theorem p9_site : ∃ _site : Site globals [] [0] [.cell 0] (fun _ => none)
    (OwnerPhaseTransitions.available []) [] [] [] selection.p9.target.expression .none cellStack
    .integer .integer cellContext root,
    RawStep ⟨outerClosedCode,.none,cellStack⟩ selection.p9.target [] [] := by
  obtain ⟨opened,_plan,_rows⟩ := opened_site
  rw [handle_shape] at opened
  obtain ⟨installed,step⟩ := opened.bind_value
    CoreCallableComposedCapturedHandle.structural_policy_stable
    (by simp [ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Code.dependencies,Instantiation.ResourceName.freeNames])
    handle_closed
  rw [p9_code] at installed
  exact ⟨installed,by change RawStep ⟨outerClosedCode,.none,cellStack⟩ ⟨selection.p9.target.expression,.none,cellStack⟩ [] []; simpa only [← handle_shape,p9_code] using step⟩

theorem original_program : ∃ program : CoreCallableInitialAdmission.Program globals (fun _ => none) []
    CoreCallableCompositionalResourceRoot.rootCode,
    CompositionalInitialAdmissionProbes.rootCheck = .ok program ∧
    HEq program.plan CoreCallableCompositionalResourceRoot.rootPlan ∧
    HEq program.rows CoreCallableCompositionalResourceRoot.rootRows ∧
    HEq program.requirements CoreCallableCompositionalResourceRoot.rootRequirements ∧
    HEq program.root root ∧ program.row = [] := by
  obtain ⟨program,accepted,plan,rows,req,account,budget⟩ :=
    CompositionalInitialAdmissionProbes.original_full_indices
  have exactRoot : root = Account.requirements (.choice .done .done) := by
    have eq : rootAccount CoreCallableCompositionalResourceRoot.initializerAnnotation body = .choice .done .done := by decide +kernel
    exact congrArg Account.requirements eq
  exact ⟨program,accepted,plan,rows,req,account.trans (heq_of_eq exactRoot.symm),budget⟩

/-- SAME executed initial Program and original acquisition chronology, with a
produced rich current Site at its computed cell0 endpoint. -/
theorem acquired_current :
    ∃ program : CoreCallableInitialAdmission.Program globals (fun _ => none) []
      CoreCallableCompositionalResourceRoot.rootCode,
      CompositionalInitialAdmissionProbes.rootCheck = .ok program ∧ HEq program.root root ∧
      ∃ _site : Site globals [] [0] [.cell 0] (fun _ => none) (OwnerPhaseTransitions.available [])
        [] [] [] selection.p9.target.expression .none cellStack .integer .integer cellContext root,
      CoreAllocationHistory.Steps graph 9 (CoreMachine.initial graph) selection.s9 ∧
      CoreInitialPrefix.Chain graph selection.p0
        [selection.p1,selection.p2,selection.p3,selection.p4,selection.p5,selection.p6,selection.p7,selection.p8,selection.p9] selection.p9 ∧
      (⟨selection.p9.target.expression,.none,cellStack⟩ : Configuration) = selection.p9.target ∧
      selection.s8.nextActivation = 0 ∧ selection.s9.nextActivation = 1 := by
  obtain ⟨program,accepted,_plan,_rows,_req,rootSame,_budget⟩ := original_program
  obtain ⟨site,_step⟩ := p9_site
  exact ⟨program,accepted,rootSame,site,
    CoreCallableComposedResourceEntry.entry_steps selection ComposedResourceRuntimeOriginProbes.initialInput,
    CoreCallableComposedResourceEntry.entry_chain selection ComposedResourceRuntimeOriginProbes.initialInput,
    rfl,rfl,rfl⟩

/-- The SAME computed activation-zero acquisition has exactly three positive Raw edges. -/
theorem acquisition_raw3 : ∃ first second : Configuration,
    RawStep selection.p8.target first [] [] ∧
    RawStep first second [.resource 0] [] ∧ RawStep second selection.p9.target [] [] :=
  CoreCallableComposedResourceEntry.acquisition_three_raw selection

#print axioms acquisition_raw3
#print axioms initializer_quiet
#print axioms initializer_account
#print axioms closed_source
#print axioms opened_site
#print axioms p9_site
#print axioms original_program
#print axioms acquired_current
end Original
end Ash.OneShot.CoreCallableOriginalResourceCurrent
