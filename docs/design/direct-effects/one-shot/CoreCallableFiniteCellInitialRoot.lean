import CoreCallableFiniteRegistryBridge
import CoreCallableFiniteResourceConsumers
import CoreCallableInitialAdmission
import CoreTranslation
namespace Ash.OneShot.CoreCallableFiniteCellInitialRoot
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

/-- The literal original full records have the exact retained CellApi scalar
shape. They remain finite original entries even before resource acquisition. -/
def entries : CoreCallableStaticProducer.OperationEntries :=
  [(.cell 0,0,.reference 0,.integer),(.cell 0,1,.pair (.reference 0) .integer,.unit)]
def policy : Syntax.TicketPolicy := fun _ => ⟨true,true⟩
def globals : Globals := ⟨CoreCallableFiniteCellRegistry.operations (some CoreCallableFiniteCellRegistry.original) entries,policy,fun _ => none⟩
def initial : CoreCallableStaticProducer.Annotation entries globals.owners [] (.integer 17) .integer [] (.request [] []) .pure Rows.pure := .integer 17

theorem original_compatibility : CoreCallableFiniteRegistryCompatibility.compatible CoreCallableFiniteCellRegistry.original entries = true := by
  simp [CoreCallableFiniteRegistryCompatibility.compatible,CoreCallableFiniteRegistryCompatibility.entryCompatible,
    CoreCallableFiniteRegistryCompatibility.readRecord,CoreCallableFiniteRegistryCompatibility.writeRecord,
    entries,CoreCallableFiniteCellRegistry.original,CoreCallableFiniteCellRegistry.CellApi.check]

theorem original_initializer_checked : ∃ receipt,
    recheck initial CoreCallableFiniteCellRegistry.original policy [] [] [] .none [] [] = .ok receipt := by
  simp only [recheck,original_compatibility]
  exact ⟨_,rfl⟩

def body := CoreCallableFiniteResourceConsumers.fullBody []
def rootCode : Code := .bind 7 (.integer 17) (.resource 3 (.integer 0)
  (.bind 9 (.resourceRef (.bound 3)) (.bind 5 (.perform (.cell (.bound 3)) 0 (.variable 9)) (.variable 7))))
def rootPlan : Plan (.sequence .pure (.sequence .pure (.resource (fun identity => body.dependencies identity)))) :=
  .sequence .pure body.resourcePlan
def rootRows : Rows (signature rootPlan) := sequenceRows Rows.pure body.resourceRows
def rootRequirements : Requirements [] := .sequence (.request [] []) (.sequence (.request [] []) body.outsideRequirements)

theorem resource_checked : resourceCheck body CoreCallableFiniteCellRegistry.original [(7,.integer)] 3 [] [] [] [(7,[])] [] = true := by
  simp [resourceCheck,openingCheck,body,CoreCallableFiniteResourceConsumers.fullBody,Body.check,LocalRef.check,
    ContractPattern.check,ContractPattern.closed,contextClosed,contextTemplate,aligned,slotContract,
    CoreCallableFiniteCellRegistry.original,CoreCallableFiniteCellRegistry.CellApi.check,nameCheck,allowedName,
    CoreCallableGraphAnnotationChecks.subsetB,CoreCallableGraphAnnotationChecks.knownB,
    Code.dependencies,ScopedPorts.Support.evaluate,LexicalBounds.environment,LexicalBounds.lookup,Syntax.without,
    effectAtoms,Instantiation.Effect.resources, Contract.port, Contract.value,
    SourcePlannedTyping.Value.erase, SourceDependencyAnnotations.Value.erase,
    CoherentSourceTypes.Value.port, ScopedPorts.Port.resources]

theorem closed_original_source : ∃ source : Source globals [] [] [] .none Environment.empty rootCode .integer [] rootRequirements rootPlan rootRows,
    Authenticated globals.registry [] source ([] : LexicalBounds) [] := by
  obtain ⟨receipt,accepted⟩ := original_initializer_checked
  obtain ⟨initializer,tree,authenticated,_⟩ := recheck_success accepted
  let resource := check_resource (entries := entries) (policy := policy) (outward := []) (owners := globals.owners)
    (scope := .none) body 0 resource_checked
  refine ⟨.bind initializer resource.source,.checked ?_ (.bind authenticated resource.auth)⟩
  simp [rootCode,Code.dependencies,effectAtoms,Instantiation.Effect.resources,Syntax.without,
    SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff,ScopedPorts.Support.evaluate]

/-- Closed raw Core graph: initializer and returned formal are connected by
actual bind and resource nodes, with the ordinary resource handle wrapper. -/
def graph : CoreSyntax.Graph := ⟨[
  CoreTranslation.Examples.node 0 (.integer 17) .integer,
  CoreTranslation.Examples.node 1 (.integer 0) .integer,
  CoreTranslation.Examples.node 2 (.variable 9) (.reference (.bound 3)),
  CoreTranslation.Examples.node 3 (.request (.cell (.bound 3)) 0 2) .integer,
  CoreTranslation.Examples.node 4 (.variable 7) .integer,
  CoreTranslation.Examples.node 5 (.bind ⟨5,.integer⟩ 3 4) .integer,
  CoreTranslation.Examples.node 6 (.resource 3 ⟨9,.reference (.bound 3)⟩ 1 5) .integer,
  CoreTranslation.Examples.node 7 (.bind ⟨7,.integer⟩ 0 6) .integer],7⟩

theorem original_graph_shape : CoreSyntax.checkShape graph = .ok () := rfl
theorem original_graph_translation : CoreTranslation.translate graph = .ok rootCode := rfl
theorem original_closed_support : rootCode.dependencies = [] := rfl

open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual

theorem certificate : SourceAdmission.Code [] (fun _ => none) []
    (OwnerPhaseTransitions.available []) [] [] rootRows Context.nil :=
  .sequence .pure (.sequence .pure (.resource (fun identity _ =>
    .sequence .pure (.sequence (.sequence .pure (.builtin (identity := identity) (by simp [select, nameValue, Selection.prepend]))) .pure))))

theorem certificate_checked : InstallationSupport.CodeChecked [] [] certificate := by
  apply InstallationSupport.CodeChecked.sequence (first := .pure)
    (second := .sequence .pure (.resource (fun identity _ =>
      .sequence .pure (.sequence (.sequence .pure (.builtin (identity := identity)
        (by simp [select, nameValue, Selection.prepend]))) .pure))))
  · exact .pure
  · apply InstallationSupport.CodeChecked.sequence (first := .pure)
      (second := .resource (fun identity _ =>
        .sequence .pure (.sequence (.sequence .pure (.builtin (identity := identity)
          (by simp [select, nameValue, Selection.prepend]))) .pure)))
    · exact .pure
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
  .bind .integer (.resource .integer (.bind .resourceRef (.bind (.perform .variable) .variable)))

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

#print axioms certificate
#print axioms certificate_checked
#print axioms initial_accounting
#print axioms initial_usage
#print axioms initial_program

#print axioms original_compatibility
#print axioms original_initializer_checked
#print axioms resource_checked
#print axioms closed_original_source
#print axioms original_graph_shape
#print axioms original_graph_translation
#print axioms original_closed_support
end Ash.OneShot.CoreCallableFiniteCellInitialRoot
