import CoreCallableGeneralResourceInitializer
import CoreCallableFiniteCellInitialRoot
import CoreCallableFiniteCellPortABI
import CoreCallableFiniteResourceConsumers
import CoreCallableInitialAdmission
import CoreTranslation
namespace Ash.OneShot.CoreCallableGeneralResourceInitialRoot
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract Environment sequenceRows)
open CoreCallableContractAdmission CoreCallableReceiverRefinement
open CoreCallableFiniteResourceTemplate CoreCallableFiniteRegistryBridge
open SourceDeclarationPlans (Plan)
open SourceDependencyAnnotations (Dependencies)
open SourcePlanSignatures (signature)
open RecursiveRequirements (Requirements)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy
set_option maxRecDepth 10000

abbrev entries := CoreCallableFiniteCellInitialRoot.entries
abbrev policy := CoreCallableFiniteCellInitialRoot.policy
abbrev globals := CoreCallableFiniteCellInitialRoot.globals
abbrev initial := CoreCallableFiniteCellInitialRoot.initial
abbrev body := CoreCallableFiniteCellInitialRoot.body
abbrev original_compatibility := CoreCallableFiniteCellInitialRoot.original_compatibility
abbrev original_initializer_checked := CoreCallableFiniteCellInitialRoot.original_initializer_checked
abbrev resource_checked := CoreCallableFiniteCellInitialRoot.resource_checked

/-- Only the SAME old resource initializer is replaced; outer7/handle9/read/
return7 and full original environments remain the prior connected root. -/
def resourceInitializer : Code := .bind 20 (.integer 0) (.variable 20)
def initializerAnnotation : CoreCallableStaticProducer.Annotation entries globals.owners [(7,.integer)]
    resourceInitializer .integer [] (.sequence (.request [] []) (.request [] []))
    (.sequence .pure .pure) (sequenceRows Rows.pure Rows.pure) :=
  .bind (.integer 0) (.variable .head)

 theorem initializer_checked : ∃ receipt,
    CoreCallableFiniteRegistryBridge.recheck initializerAnnotation CoreCallableFiniteCellRegistry.original
      policy [] [] [] .none [(7,[])] [] = .ok receipt := ⟨_,rfl⟩

 theorem general_resource_checked : ∃ receipt,
    CoreCallableGeneralResourceInitializer.check initializerAnnotation body CoreCallableFiniteCellRegistry.original
      policy [] [] [] [] .none 3 [(7,[])] [] = .ok receipt := ⟨_,rfl⟩

def rootCode : Code := .bind 7 (.integer 17) ( .resource 3 resourceInitializer
  (.bind 9 (.resourceRef (.bound 3)) (.bind 5 (.perform (.cell (.bound 3)) 0 (.variable 9)) (.variable 7))))
def rootPlan : Plan (.sequence .pure (.sequence (.sequence .pure .pure) (.resource (fun identity => body.dependencies identity)))) :=
  .sequence .pure (CoreCallableGeneralResourceInitializer.combinedPlan body (.sequence .pure .pure))
def rootRows : Rows (signature rootPlan) := sequenceRows Rows.pure (CoreCallableGeneralResourceInitializer.combinedRows body (sequenceRows Rows.pure Rows.pure))
def rootRequirements : Requirements [] := .sequence (.request [] []) (.sequence (.sequence (.request [] []) (.request [] [])) body.outsideRequirements)

theorem closed_original_source : ∃ source : Source globals [] [] [] .none Environment.empty rootCode .integer [] rootRequirements rootPlan rootRows,
    Authenticated globals.registry [] source ([] : LexicalBounds) [] := by
  obtain ⟨receipt,accepted⟩ := original_initializer_checked
  obtain ⟨initializer,tree,authenticated,_⟩ := recheck_success accepted
  obtain ⟨resourceReceipt,resourceAccepted⟩ := general_resource_checked
  let resource := CoreCallableGeneralResourceInitializer.check_success resourceAccepted
  refine ⟨.bind initializer resource.source,.checked ?_ (.bind authenticated resource.authenticated)⟩
  simp [rootCode,resourceInitializer,Code.dependencies,effectAtoms,Instantiation.Effect.resources,Syntax.without,
    SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff,ScopedPorts.Support.evaluate]

/-- Closed raw Core graph: initializer and returned formal are connected by
actual bind and resource nodes, with the ordinary resource handle wrapper. -/
def graph : CoreSyntax.Graph := ⟨[
  CoreTranslation.Examples.node 0 (.integer 17) .integer,
  CoreTranslation.Examples.node 1 (.integer 0) .integer,
  CoreTranslation.Examples.node 2 (.variable 20) .integer,
  CoreTranslation.Examples.node 3 (.bind ⟨20,.integer⟩ 1 2) .integer,
  CoreTranslation.Examples.node 4 (.variable 9) (.reference (.bound 3)),
  CoreTranslation.Examples.node 5 (.request (.cell (.bound 3)) 0 4) .integer,
  CoreTranslation.Examples.node 6 (.variable 7) .integer,
  CoreTranslation.Examples.node 7 (.bind ⟨5,.integer⟩ 5 6) .integer,
  CoreTranslation.Examples.node 8 (.resource 3 ⟨9,.reference (.bound 3)⟩ 3 7) .integer,
  CoreTranslation.Examples.node 9 (.bind ⟨7,.integer⟩ 0 8) .integer],9⟩

theorem original_graph_shape : CoreSyntax.checkShape graph = .ok () := rfl
theorem original_graph_translation : CoreTranslation.translate graph = .ok rootCode := rfl
theorem original_closed_support : rootCode.dependencies = [] := rfl

open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual

theorem certificate : SourceAdmission.Code [] (fun _ => none) []
    (OwnerPhaseTransitions.available []) [] [] rootRows Context.nil :=
  .sequence .pure (.sequence (.sequence .pure .pure) (.resource (fun identity _ =>
    .sequence .pure (.sequence (.sequence .pure (.builtin (identity := identity) (by simp [select, nameValue, Selection.prepend]))) .pure))))

theorem certificate_checked : InstallationSupport.CodeChecked [] [] certificate := by
  apply InstallationSupport.CodeChecked.sequence (first := .pure)
    (second := .sequence (.sequence .pure .pure) (.resource (fun identity _ =>
      .sequence .pure (.sequence (.sequence .pure (.builtin (identity := identity)
        (by simp [select, nameValue, Selection.prepend]))) .pure))))
  · exact .pure
  · apply InstallationSupport.CodeChecked.sequence (first := .sequence .pure .pure)
      (second := .resource (fun identity _ =>
        .sequence .pure (.sequence (.sequence .pure (.builtin (identity := identity)
          (by simp [select, nameValue, Selection.prepend]))) .pure)))
    · exact .sequence .pure .pure
    · apply InstallationSupport.CodeChecked.resource (body := fun identity _ =>
        .sequence .pure (.sequence (.sequence .pure (.builtin (identity := identity)
          (by simp [select, nameValue, Selection.prepend]))) .pure))
      intro identity fresh
      apply InstallationSupport.CodeChecked.sequence (first := .pure)
        (second := .sequence (.sequence .pure (.builtin (identity := identity)
          (by simp [select, nameValue, Selection.prepend]))) .pure)
      · exact .pure
      · apply InstallationSupport.CodeChecked.sequence (first := .sequence .pure
          (.builtin (identity := identity) (by simp [select, nameValue, Selection.prepend])))
          (second := .pure)
        · apply InstallationSupport.CodeChecked.sequence (first := .pure)
            (second := .builtin (identity := identity) (by simp [select, nameValue, Selection.prepend]))
          · exact .pure
          · exact InstallationSupport.CodeChecked.builtin
              (identity := identity) (found := by simp [select, nameValue, Selection.prepend])
        · exact .pure

theorem initial_accounting : Accounting.Run [] [] rootRows Context.nil (.request [] []) := by
  apply Accounting.Run.sequence
  apply Accounting.Run.pure
  apply Accounting.Wait.plain
  apply Accounting.Run.sequence
  apply Accounting.Run.sequence
  apply Accounting.Run.pure
  apply Accounting.Wait.plain
  apply Accounting.Run.pure
  apply Accounting.Wait.plain
  apply Accounting.Run.installResource
  intro identity fresh
  apply Accounting.Run.sequence
  apply Accounting.Run.pure
  apply Accounting.Wait.plain
  apply Accounting.Run.sequence
  apply Accounting.Run.sequence
  apply Accounting.Run.pure
  apply Accounting.Wait.plain
  apply Accounting.Run.builtin (identity := identity)
  · simp [select, nameValue, Selection.prepend]
  · exact .plain (.pure (.cell .nil))

theorem initial_usage : Uses globals.policy .none .available rootCode .available :=
  .bind .integer (.resource (.bind .integer .variable) (.bind .resourceRef (.bind (.perform .variable) .variable)))

theorem initial_program : ∃ _ : CoreCallableInitialAdmission.Program globals (fun _ => none) [] rootCode, True := by
  obtain ⟨source,authenticated⟩ := closed_original_source
  refine ⟨{
    result := .integer
    dependencies := _
    plan := rootPlan
    rows := rootRows
    demand := []
    requirements := rootRequirements
    source := source
    authenticated := authenticated
    support := ?_
    usage := initial_usage
    certificate := certificate
    certificateChecked := certificate_checked
    rootDemand := []
    root := .request [] []
    accounting := initial_accounting
    annotated := .request [] []
    annotation := .original
    row := []
    checked := .request (by rfl)
    bounded := List.Subset.refl _ }, trivial⟩
  simp [SourceSupport.bounds_iff, original_closed_support, ScopedPorts.Support.evaluate]

/-- Same finite Program output and existing port ABI produce a calculus step;
this is not a claim of Rust/Core validated execution or generic admission. -/
theorem same_root_initial_step :
    ∃ program : CoreCallableInitialAdmission.Program globals (fun _ => none) [] rootCode,
      ∃ registry after,
        NamedAccessStep [] ⟨⟨⟨rootCode,.none,.nil⟩,[],[]⟩,[]⟩ after ∧
        ScopedPortJoint.Valid (CoreCallableContractExecution.lowerOperations globals).ports
          policy registry [] after program.result.port [] := by
  obtain ⟨program,_⟩ := initial_program
  have builtins := CoreCallableFiniteCellPortABI.compatibility_port_abi
    (policy := policy) (owners := globals.owners) original_compatibility
  rcases program.initial_progress builtins with value | ⟨registry,after,step,joint⟩
  · cases value
  · exact ⟨program,registry,after,step,joint⟩

theorem initializer_is_not_value : ¬ resourceInitializer.IsValue := by simp [resourceInitializer,Code.IsValue]

/-- Typed original annotation with unsupported finite recipe: actual recursive
initializer checking fails before the resource/body check. -/
def rejectedLambda : CoreCallableStaticProducer.Annotation entries globals.owners [(7,.integer)]
    (.lambda 21 (.integer 0)) (.function .unit .integer [] [] .pure Rows.pure)
    [] (.request [] []) .pure Rows.pure :=
  .lambda (.integer 0) (.unsupported .pure) (.identity Rows.pure)
def rejectedInitializer : CoreCallableStaticProducer.Annotation entries globals.owners [(7,.integer)]
    (.app (.lambda 21 (.integer 0)) .unit) .integer []
    (.emitAfter (.sequence (.request [] []) (.request [] [])) [] [])
    (.sequence .pure (.sequence .pure .pure))
    (sequenceRows Rows.pure (sequenceRows Rows.pure Rows.pure)) :=
  .app rejectedLambda .unit .pure

theorem unsupported_recipe_propagated :
    CoreCallableGeneralResourceInitializer.check rejectedInitializer body CoreCallableFiniteCellRegistry.original
      policy [] [] [] [] .none 3 [(7,[])] [] =
      .error (.initializer (.originalCheck .unsupportedRecipe)) := rfl

theorem invalid_api_rejected :
    CoreCallableGeneralResourceInitializer.check initializerAnnotation body
      {CoreCallableFiniteCellRegistry.original with binder := 1}
      policy [] [] [] [] .none 3 [(7,[])] [] = .error (.initializer .incompatibleRegistry) := rfl

theorem fresh_reference_escape_rejected :
    CoreCallableGeneralResourceInitializer.check initializerAnnotation
      (.reference (.bound 3) : Body [(7,.slot 0)] (.resourceRef (.bound 3)) (.reference (.bound 3)))
      CoreCallableFiniteCellRegistry.original policy [] [] [] [] .none 3 [(7,[])] [] = .error .resourceBody := rfl

#print axioms initializer_checked
#print axioms general_resource_checked
#print axioms closed_original_source
#print axioms original_graph_shape
#print axioms original_graph_translation
#print axioms original_closed_support
#print axioms certificate
#print axioms certificate_checked
#print axioms initial_accounting
#print axioms initial_usage
#print axioms initial_program
#print axioms same_root_initial_step
#print axioms initializer_is_not_value
#print axioms unsupported_recipe_propagated
#print axioms invalid_api_rejected
#print axioms fresh_reference_escape_rejected
end Ash.OneShot.CoreCallableGeneralResourceInitialRoot
