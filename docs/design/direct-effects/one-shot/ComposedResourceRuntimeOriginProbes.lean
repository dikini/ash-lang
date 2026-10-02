import CoreCallableComposedRuntimeBindings
import ComposedResourceOriginProbes
namespace Ash.OneShot.ComposedResourceRuntimeOriginProbes
open ScopedExpressions ScopedExecution CoreSyntax CoreTranslation CoreMachine CoreValueRelation
open CoreCallableComposedResourceEntry CoreCallableComposedRuntimeBindings
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def rawBody : Code := match CoreCallableCompositionalResourceRoot.codeOf CoreCallableCompositionalResourceRoot.body with | .bind _ _ body => body | _ => .unit
def rawFunction : Code := match CoreCallableCompositionalResourceRoot.codeOf CoreCallableCompositionalResourceRoot.reader with | .lambda _ body => body | _ => .unit
def rawTail : Code := match rawBody with | .bind _ _ body => body | _ => .unit

def selection : Selection CoreCallableCompositionalResourceRoot.graph where
  outer := ⟨7,.integer⟩
  outerSite := 0
  resourceSite := 21
  initializerSite := 3
  initializerLiteral := 1
  initializerVariable := 2
  bodySite := 20
  inner := ⟨20,.integer⟩
  resource := 3
  handle := ⟨9,.reference (.bound 3)⟩
  outerValue := 17
  payload := 0
  rootNode := CoreTranslation.Examples.node 22 (.bind ⟨7,.integer⟩ 0 21) .integer
  outerNode := CoreTranslation.Examples.node 0 (.integer 17) .integer
  resourceNode := CoreTranslation.Examples.node 21 (.resource 3 ⟨9,.reference (.bound 3)⟩ 3 20) .integer
  initializerNode := CoreTranslation.Examples.node 3 (.bind ⟨20,.integer⟩ 1 2) .integer
  literalNode := CoreTranslation.Examples.node 1 (.integer 0) .integer
  variableNode := CoreTranslation.Examples.node 2 (.variable 20) .integer
  rawBody := rawBody
  fuel := 24
  rootKnown := rfl
  rootKind := rfl
  outerKnown := rfl
  outerKind := rfl
  resourceKnown := rfl
  resourceKind := rfl
  initializerKnown := rfl
  initializerKind := rfl
  literalKnown := rfl
  literalKind := rfl
  variableKnown := rfl
  variableKind := rfl
  bodyTranslated := rfl
  resourceTranslated := rfl
  outerTranslated := rfl
  initialTranslated := rfl
  literalTranslated := rfl
  variableTranslated := rfl
  innerDifferent := by decide
  handleDifferent := by decide
  outerReady := by
    intro name member
    change Syntax.Dependency.variable name ∈ [.variable 7,.variable 7] at member
    simpa using member
  bodyReady := by
    intro name member
    change Syntax.Dependency.variable name ∈ [.variable 9] at member
    simpa using member
  outerNoTicket := rfl
  resourceNoTicket := rfl
  resourceClosed := rfl

theorem initialInput : CoreCallableInitialChronology.InitialInput CoreCallableCompositionalResourceRoot.graph selection.rootCode :=
  initial_from_checked CoreCallableComposedResourceOrigins.Probes.originalGraphPrefix

def reader : ReaderSelection selection where
  binder := ⟨12,CoreCallableCompositionalResourceRoot.readerType⟩
  parameter := ⟨10,.unit⟩
  binderType := rfl
  functionSite := 6
  functionBody := 5
  tailSite := 19
  node := CoreTranslation.Examples.node 20 (.bind ⟨12,CoreCallableCompositionalResourceRoot.readerType⟩ 6 19) .integer
  functionNode := CoreTranslation.Examples.node 6 (.function ⟨10,.unit⟩ 5) CoreCallableCompositionalResourceRoot.readerType
  rawFunction := rawFunction
  rawTail := rawTail
  fuel := 24
  fnFuel := 24
  known := rfl
  kind := rfl
  functionKnown := rfl
  functionKind := rfl
  functionTranslated := rfl
  tailTranslated := rfl
  rawSame := rfl
  outerDifferent := by decide
  handleDifferent := by decide
  ready := by
    intro name member
    change Syntax.Dependency.variable name ∈ [.variable 12] at member
    simpa using member
  noTicket := rfl

theorem reader_executed : ∃ checked, produce_reader reader = .ok checked := by
  exact ⟨_,rfl⟩

noncomputable def checkedReader := Classical.choose reader_executed

theorem initial_to_reader : CoreAllocationHistory.Steps CoreCallableCompositionalResourceRoot.graph 12
    (CoreMachine.initial CoreCallableCompositionalResourceRoot.graph) reader.s12 := installed_steps selection reader initialInput checkedReader

theorem exact_installed_environment : reader.installedEnvironment =
    .binding 12 (.closure 10 5 (.binding 9 (.handle 0) (.resource 3 0 (.binding 7 (.integer 17) .empty))))
      (.binding 9 (.handle 0) (.resource 3 0 (.binding 7 (.integer 17) .empty))) := rfl

theorem exact_closure_value : ValueRel CoreCallableCompositionalResourceRoot.graph [] []
    (.closure 10 5 selection.acquiredEnvironment) reader.initializer :=
  reader_value selection reader initialInput checkedReader

theorem actual_reader_lookup : reader.installedEnvironment.lookup 12 =
    some (.closure 10 5 selection.acquiredEnvironment) := installed_lookup selection reader

theorem incorrect_installed_value_rejected : reader.installedEnvironment.lookup 12 ≠ some (.integer 17) := by
  rw [actual_reader_lookup]
  intro impossible
  cases impossible

open CoreCallableComposedResourceOrigins CoreCallableComposedCapturedHandle
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

/-- Execute the original closed-handle checks at the runtime-computed owner,
using the same retained whole outside rich and storage maps. -/
theorem handle_at_computed_owner (staticReader : CoreCallableComposedResourceOrigins.Probes.ReaderPath opened) :
    ∃ handle, capture_handle staticReader.path selection.s8.nextActivation (by simp) = .ok handle := by
  have rich : ∃ receipt, CoreCallableFiniteRegistryBridge.recheck
      (CoreCallableStaticProducer.Annotation.reference
        (entries := CoreCallableComposedResourceOrigins.Probes.Original.entries)
        (owners := CoreCallableComposedResourceOrigins.Probes.Original.globals.owners)
        (bindings := [(7,.integer)]) 0)
      CoreCallableComposedResourceOrigins.Probes.Original.api
      CoreCallableComposedResourceOrigins.Probes.Original.policy [] [0] [.cell 0] .none [(7,[])] [0] = .ok receipt := ⟨_,rfl⟩
  obtain ⟨receipt,accepted⟩ := rich
  have stored : CoreCallableReturnStorageProducer.check [(7,.storage [])] (.resourceRef (.activation 0))
      (.node (some (.storage [0])) []) = some (.storage [0]) := by
    simp [CoreCallableReturnStorageProducer.check,CoreCallableReturnStorageProducer.captureCheck,
      CoreCallableReturnStorageProducer.atomCheck,Code.dependencies]
  exact capture_handle_success (path := staticReader.path) accepted stored

/-- This single connected witness executes the original static prefix/opening,
retains its reader constructor path, and joins the full changed private family
and lower receipt to the actual twelve-edge initial Core chronology. -/
theorem original_runtime_join :
    ∃ opened : CoreCallableComposedResourceOrigins.Probes.Opened,
    ∃ staticReader : CoreCallableComposedResourceOrigins.Probes.ReaderPath opened,
    ∃ current : PLift (Current staticReader.path selection.s8.nextActivation (by simp)),
    ∃ handle : PLift (CapturedHandle staticReader.path selection.s8.nextActivation (by simp)),
    ∃ joined : PLift (PairedReader reader current.down handle.down),
      produce_graph_prefix CoreCallableCompositionalResourceRoot.graph
        CoreCallableComposedResourceOrigins.Probes.originalPath
        CoreCallableComposedResourceOrigins.Probes.Original.api
        CoreCallableComposedResourceOrigins.Probes.Original.policy
        CoreCallableComposedResourceOrigins.Probes.Original.declarations [] [] [] .none [] =
        .ok CoreCallableComposedResourceOrigins.Probes.originalGraphPrefix ∧
      produce_opened CoreCallableComposedResourceOrigins.Probes.originalPrefix
        CoreCallableComposedResourceOrigins.Probes.Original.annotation
        CoreCallableComposedResourceOrigins.Probes.Original.body
        CoreCallableComposedResourceOrigins.Probes.Original.initialRecipe
        CoreCallableComposedResourceOrigins.Probes.Original.bodyRecipe [] [] = .ok opened ∧
      produce_current staticReader.path selection.s8.nextActivation (by simp) = some current ∧
      capture_handle staticReader.path selection.s8.nextActivation (by simp) = .ok handle ∧
      pair_reader reader initialInput checkedReader current.down handle.down = .ok joined ∧
      CoreAllocationHistory.Steps CoreCallableCompositionalResourceRoot.graph 12
        (CoreMachine.initial CoreCallableCompositionalResourceRoot.graph) reader.s12 ∧
      reader.installedEnvironment.lookup 12 = some (.closure 10 5 selection.acquiredEnvironment) := by
  obtain ⟨opened,openedAccepted⟩ := CoreCallableComposedResourceOrigins.Probes.resource_executed
  obtain ⟨staticReader,_⟩ := CoreCallableComposedResourceOrigins.Probes.connected_reader opened
  obtain ⟨current,currentAccepted⟩ := CoreCallableComposedResourceOrigins.Probes.reader_current_all_fresh staticReader selection.s8.nextActivation
  obtain ⟨handle,handleAccepted⟩ := handle_at_computed_owner staticReader
  obtain ⟨joined,joinedAccepted⟩ := pair_reader_success reader initialInput checkedReader current.down handle.down (by rfl) (by rfl) (by rfl)
  exact ⟨opened,staticReader,current,handle,joined,
    CoreCallableComposedResourceOrigins.Probes.original_graph_prefix_executed,
    openedAccepted,currentAccepted,handleAccepted,joinedAccepted,
    initial_to_reader,actual_reader_lookup⟩

theorem computed_owner_ledger : selection.s8.nextActivation = 0 ∧
    reader.s12.nextActivation = 1 ∧ CoreAllocationHistory.History reader.s12 :=
  ⟨rfl,installed_activation selection reader initialInput checkedReader⟩

theorem reader_plain_metadata : reader.plain.input =
    .function .unit .integer [.cell 0] [0,0] := rfl

#print axioms computed_owner_ledger
#print axioms reader_plain_metadata
#print axioms reader_executed
#print axioms initial_to_reader
#print axioms exact_installed_environment
#print axioms exact_closure_value
#print axioms actual_reader_lookup
#print axioms incorrect_installed_value_rejected
#print axioms handle_at_computed_owner
#print axioms original_runtime_join
end Ash.OneShot.ComposedResourceRuntimeOriginProbes
