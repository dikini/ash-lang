import CoreCallableComposedCapturedHandle
import CompositionalResourceStorageProbes
namespace Ash.OneShot.CoreCallableComposedResourceOrigins.Probes
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractAdmission CoreCallableReceiverRefinement
open CoreCallableComposedResourceOrigins
open CoreCallableComposedCapturedHandle
open CoreCallableCompositionalResourceBody
namespace Original
abbrev entries := CoreCallableCompositionalResourceRoot.entries
abbrev globals := CoreCallableCompositionalResourceRoot.globals
abbrev policy := CoreCallableCompositionalResourceRoot.policy
abbrev root := CoreCallableCompositionalResourceRoot.rootCode
abbrev body := CoreCallableCompositionalResourceRoot.body
abbrev annotation := CoreCallableCompositionalResourceRoot.initializerAnnotation
abbrev api := CoreCallableFiniteCellRegistry.original
abbrev declarations := CoreCallableCompositionalResourceStorage.Probes.declarations
abbrev bodyRecipe := CoreCallableCompositionalResourceStorage.Probes.bodyRecipe
abbrev initialRecipe := CoreCallableCompositionalResourceStorage.Probes.initializerRecipe
end Original
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

def originalPath := Prefix.bind (parameter := 7) (root := Original.root) Prefix.here
  CoreCallableFiniteCellInitialRoot.initial (.node (some (.storage [])) [])

noncomputable def originalRich := Classical.choose CoreCallableFiniteCellInitialRoot.original_initializer_checked

def originalPrefix : CheckedOriginalPrefix originalPath Original.api Original.policy Original.declarations [] [] [] .none [] :=
  ⟨[(7,.storage [])],[(7,[])],CoreCallableCompositionalResourceStorage.Probes.records,
    .bind .here (Classical.choose_spec CoreCallableFiniteCellInitialRoot.original_initializer_checked)
      (by simp [CoreCallableStorageRecipes.specialize,CoreCallableStorageRecipes.specializeList,CoreCallableStorageRecipes.contract,CoreCallableStorageRecipes.bound,CoreCallableCompositionalResourceStorage.Probes.outerAnnotation]) CoreCallableCompositionalResourceStorage.Probes.original_storage_initializer_checked (List.nil_subset _)⟩

theorem prefix_executed : produce_prefix originalPath Original.api Original.policy Original.declarations [] [] [] .none [] = .ok originalPrefix := by
  dsimp only [originalPath,produce_prefix]
  dsimp only [Bind.bind,Except.bind]
  split
  · rename_i failed
    have accepted := Classical.choose_spec CoreCallableFiniteCellInitialRoot.original_initializer_checked
    have bad := failed.symm.trans accepted
    cases bad
  · split
    · rename_i failed
      have specialized : CoreCallableStorageRecipes.specialize [] Instantiation.Environment.empty
          (.node (some (.storage [])) []) = some CoreCallableCompositionalResourceStorage.Probes.outerAnnotation := by
        simp [CoreCallableStorageRecipes.specialize,CoreCallableStorageRecipes.specializeList,
          CoreCallableStorageRecipes.contract,CoreCallableStorageRecipes.bound,CoreCallableCompositionalResourceStorage.Probes.outerAnnotation]
      rw [failed] at specialized
      contradiction
    · rename_i storedAnnotation specialized
      have same : storedAnnotation = CoreCallableCompositionalResourceStorage.Probes.outerAnnotation := by
        have known : CoreCallableStorageRecipes.specialize [] Instantiation.Environment.empty
            (.node (some (.storage [])) []) = some CoreCallableCompositionalResourceStorage.Probes.outerAnnotation := by
          simp [CoreCallableStorageRecipes.specialize,CoreCallableStorageRecipes.specializeList,
            CoreCallableStorageRecipes.contract,CoreCallableStorageRecipes.bound,CoreCallableCompositionalResourceStorage.Probes.outerAnnotation]
        exact Option.some.inj (specialized.symm.trans known)
      subst storedAnnotation
      split
      · rename_i failed
        have checked := CoreCallableCompositionalResourceStorage.Probes.original_storage_initializer_checked
        rw [failed] at checked
        contradiction
      · rename_i stored checked
        have same := Option.some.inj (checked.symm.trans CoreCallableCompositionalResourceStorage.Probes.original_storage_initializer_checked)
        subst stored
        simp only [CallableContracts.Contract.storageOf,List.nil_subset,decide_true]
        rfl

theorem prefix_full_maps : originalPrefix.storage = [(7,.storage [])] ∧ originalPrefix.lexical = [(7,[])] ∧
    originalPrefix.records = CoreCallableCompositionalResourceStorage.Probes.records := ⟨rfl,rfl,rfl⟩

theorem resource_executed : ∃ opened,
    produce_opened originalPrefix Original.annotation Original.body Original.initialRecipe Original.bodyRecipe [] [] = .ok opened := by
  obtain ⟨source,sourceAccepted⟩ := CoreCallableCompositionalResourceRoot.compositional_checked
  obtain ⟨opened,openedAccepted⟩ := CoreCallableCompositionalResourceStorage.Probes.body_opening_checked
  obtain ⟨combined,accepted⟩ := CoreCallableCompositionalResourceStorage.check_composed_accepted
    (current := originalPrefix.origins) sourceAccepted
    CoreCallableCompositionalResourceStorage.Probes.original_resource_initializer_checked openedAccepted (List.nil_subset _)
  exact produce_opened_accepted accepted

abbrev Opened := ResourceOpened originalPrefix Original.annotation Original.body Original.initialRecipe Original.bodyRecipe [] []
abbrev readerRecipe : CoreCallableCompositionalResourceStorage.Recipe := .lambda (.storage []) (.cell .variable)
abbrev readerStorage : CoreCallableCompositionalResourceStorage.Bindings := [(9,.storage [.fresh]),(7,.storage [])]

structure ReaderPath (opened : Opened) where
  stored : CoreCallableCompositionalResourceStorage.Tree
  produced : CoreCallableCompositionalResourceStorage.Produced Original.api 3 [] readerStorage
    (CoreCallableCompositionalResourceRoot.codeOf CoreCallableCompositionalResourceRoot.reader) stored
  path : OpenedBind opened CoreCallableCompositionalResourceRoot.reader produced readerRecipe [9]

 theorem connected_reader (opened : Opened) : ∃ _reader : ReaderPath opened, True := by
  obtain ⟨firstStep,_accepted⟩ := produce_bind_success (OpenedBind.here (opened := opened))
  rcases firstStep with ⟨inputStored,stored,initialProduced,tailProduced,initialAccepted,tailAccepted,selected,continuation⟩
  have actual : CoreCallableCompositionalResourceStorage.check Original.api 3 []
      (CoreCallableCompositionalResourceStorage.original originalPrefix.storage)
      (.resourceRef (.bound 3)) .leaf = some ⟨.storage [.fresh],.reference rfl rfl⟩ := by
    simp [CoreCallableCompositionalResourceStorage.check,CoreCallableCompositionalResourceStorage.nameAtom,CoreCallableCompositionalResourceStorage.Atom.valid]
  have same : inputStored = .storage [.fresh] :=
    (congrArg Sigma.fst (Option.some.inj (actual.symm.trans initialAccepted))).symm
  subst inputStored
  obtain ⟨readerStep,_accepted⟩ := produce_bind_success continuation
  exact ⟨⟨readerStep.inputStored,readerStep.initialProduced,readerStep.selected⟩,True.intro⟩

abbrev readerResult : CoreCallableCompositionalResourceStorage.Tree :=
  .function [.fresh,.fresh] (.storage []) (.storage [])

set_option linter.unusedSimpArgs false in
theorem reader_checked : ∃ produced,
    CoreCallableCompositionalResourceStorage.check Original.api 3 [] readerStorage
      (CoreCallableCompositionalResourceRoot.codeOf CoreCallableCompositionalResourceRoot.reader) readerRecipe = some ⟨readerResult,produced⟩ := by
  dsimp only [CoreCallableCompositionalResourceRoot.codeOf,CoreCallableCompositionalResourceRoot.reader,
    CoreCallableCompositionalResourceRoot.oldRead,readerRecipe,readerResult,readerStorage,Original.api]
  repeat' (first
    | dsimp [CoreCallableCompositionalResourceStorage.lookup,CoreCallableCompositionalResourceStorage.Tree.valid,
        CoreCallableCompositionalResourceStorage.Atom.valid,CoreCallableCompositionalResourceStorage.template,
        CoreCallableCompositionalResourceStorage.template.bounds,CoreCallableCompositionalResourceStorage.captures,
        CoreCallableCompositionalResourceStorage.collect,CoreCallableCompositionalResourceStorage.Tree.storageOf,
        CoreCallableCompositionalResourceStorage.nameAtom,Code.dependencies,Code.freeNames,
        CoreCallableFiniteCellRegistry.CellApi.check,CoreCallableFiniteCellRegistry.original,Syntax.without,
        Instantiation.Effect.resources,Instantiation.Effect.freeNames,Instantiation.ResourceName.freeNames]
    | simp only [CoreCallableCompositionalResourceStorage.check])
  exact ⟨_,rfl⟩

theorem reader_full_storage (reader : ReaderPath opened) : reader.stored = readerResult := by
  obtain ⟨produced,actual⟩ := reader_checked
  exact (congrArg Sigma.fst (Option.some.inj (actual.symm.trans reader.path.accepted))).symm

theorem reader_current_all_fresh (reader : ReaderPath opened) (identity : Nat) :
    ∃ receipt, produce_current reader.path identity (by simp) = some receipt := by
  apply produce_current_success
  · rfl
  · rfl
  · rfl
  · simp [lexicalAfter,Code.instantiate,Code.dependencies,Syntax.without,
      CoreCallableCompositionalResourceRoot.codeOf,
      CoreCallableCompositionalResourceRoot.oldRead,ScopedPorts.Support.evaluate,
      LexicalBounds.environment,LexicalBounds.lookup,LexicalBounds.extend,
      CoreCallableGraphAnnotationChecks.subsetB,Instantiation.Effect.instantiate,
      Instantiation.ResourceName.instantiate,Instantiation.Environment.bind,effectAtoms,Instantiation.Effect.resources]

theorem handle_executed (reader : ReaderPath opened) :
    ∃ handle, capture_handle reader.path 1 (by simp) = .ok handle := by
  have rich : ∃ receipt, CoreCallableFiniteRegistryBridge.recheck
      (CoreCallableStaticProducer.Annotation.reference (entries := Original.entries) (owners := Original.globals.owners)
        (bindings := [(7,.integer)]) 1) Original.api Original.policy [] [1] [.cell 1] .none [(7,[])] [1] = .ok receipt := ⟨_,rfl⟩
  obtain ⟨receipt,accepted⟩ := rich
  have stored : CoreCallableReturnStorageProducer.check [(7,.storage [])] (.resourceRef (.activation 1))
      (.node (some (.storage [1])) []) = some (.storage [1]) := by
    simp [CoreCallableReturnStorageProducer.check,CoreCallableReturnStorageProducer.captureCheck,CoreCallableReturnStorageProducer.atomCheck,Code.dependencies]
  exact capture_handle_success (path := reader.path) accepted stored

abbrev higherRecipe : CoreCallableCompositionalResourceStorage.Recipe := .lambda (.slot 12) (.app .variable .leaf)
abbrev higherStorage : CoreCallableCompositionalResourceStorage.Bindings := (12,readerResult)::readerStorage

structure HigherPath (opened : Opened) where
  stored : CoreCallableCompositionalResourceStorage.Tree
  produced : CoreCallableCompositionalResourceStorage.Produced Original.api 3 [] higherStorage
    (CoreCallableCompositionalResourceRoot.codeOf CoreCallableCompositionalResourceRoot.higherOrder) stored
  path : OpenedBind opened CoreCallableCompositionalResourceRoot.higherOrder produced higherRecipe [12,9]

theorem connected_higher (opened : Opened) : ∃ _higher : HigherPath opened, True := by
  obtain ⟨firstStep,_accepted⟩ := produce_bind_success (OpenedBind.here (opened := opened))
  rcases firstStep with ⟨inputStored,stored,initialProduced,tailProduced,initialAccepted,tailAccepted,selected,continuation⟩
  have actual : CoreCallableCompositionalResourceStorage.check Original.api 3 []
      (CoreCallableCompositionalResourceStorage.original originalPrefix.storage)
      (.resourceRef (.bound 3)) .leaf = some ⟨.storage [.fresh],.reference rfl rfl⟩ := by
    simp [CoreCallableCompositionalResourceStorage.check,CoreCallableCompositionalResourceStorage.nameAtom,CoreCallableCompositionalResourceStorage.Atom.valid]
  have same : inputStored = .storage [.fresh] :=
    (congrArg Sigma.fst (Option.some.inj (actual.symm.trans initialAccepted))).symm
  subst inputStored
  obtain ⟨readerStep,_accepted⟩ := produce_bind_success continuation
  rcases readerStep with ⟨readerInputStored,readerTailStored,readerProduced,readerTailProduced,readerAccepted,readerTailAccepted,readerSelected,readerContinuation⟩
  obtain ⟨actualReader,actualReaderAccepted⟩ := reader_checked
  have exactReader : readerInputStored = readerResult :=
    (congrArg Sigma.fst (Option.some.inj (actualReaderAccepted.symm.trans readerAccepted))).symm
  subst readerInputStored
  obtain ⟨higherStep,_accepted⟩ := produce_bind_success readerContinuation
  exact ⟨⟨higherStep.inputStored,higherStep.initialProduced,higherStep.selected⟩,True.intro⟩

theorem higher_current_all_fresh (higher : HigherPath opened) (identity : Nat) :
    ∃ receipt, produce_current higher.path identity (by simp) = some receipt := by
  apply produce_current_success
  · rfl
  · rfl
  · rfl
  · rfl

abbrev changedReader : Code := .perform (.cell (.activation 1)) 0 (.resourceRef (.activation 1))
abbrev privateChecking := Checking.embedded CoreCallableCompositionalResourceRoot.oldRead
abbrev ReaderFamily (next : Code) := CoreCallableCapturedLambdaConstructor.Family
  Original.globals.registry [] Original.globals.owners [1]
  (CoreCallableStaticProducer.environment [(7,.integer)]) 10 next
  .unit .integer [.cell 1] [⟨.cell 1,0,false⟩] (privateChecking.plan 1) (privateChecking.rows 1)

theorem original_closed_reader (reader : ReaderPath opened) :
    ∃ family : ReaderFamily changedReader,
      Authenticated Original.globals.registry [] (family.whole (allowed := [.cell 1]) (scope := .none)) [(7,[])] [1] ∧
      CallableContracts.Derives Original.declarations
        (CoreCallableReturnStorageProducer.environment [(7,.storage [])]) [1] .none
        (.lambda 10 changedReader) (.function [1,1] (.storage []) (.storage [])) ∧
      ∃ current : Current reader.path 1 (by simp), ∃ handle : CapturedHandle reader.path 1 (by simp),
      ∃ replacement : IndexedSource Original.globals.registry [] Original.globals.owners [1] [.cell 1] .none
        (CoreCallableStaticProducer.environment [(7,.integer)]) (.resourceRef (.activation 1)) (.reference 1)
        [] (.request [] []) .pure SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Rows.pure,
      CoreCallableCapturedLambdaConstructor.Receipt current.source replacement structural_policy_stable handle.closed changedReader family := by
  obtain ⟨current,_accepted⟩ := reader_current_all_fresh reader 1
  obtain ⟨handle,_accepted⟩ := handle_executed reader
  obtain ⟨next,family,replacement,receipt,same,auth,lower⟩ := close_reader_handle current.down handle.down
  have deterministic : Code.lambda 10 next = .lambda 10 changedReader := by
    simpa [CoreCallableCompositionalResourceRoot.codeOf,CoreCallableCompositionalResourceRoot.reader,
      CoreCallableCompositionalResourceRoot.oldRead,Code.instantiate,Code.subst,Instantiation.Effect.instantiate,
      Instantiation.ResourceName.instantiate,Instantiation.Environment.bind,Instantiation.Environment.empty,changedReader] using same
  have exactCode : next = changedReader := (Code.lambda.inj deterministic).2
  subst next
  refine ⟨family,auth,?_,current.down,handle.down,replacement,receipt⟩
  simpa only [reader_full_storage reader,CoreCallableCompositionalResourceStorage.Tree.value,
    CoreCallableCompositionalResourceStorage.Atom.value,List.map_cons,List.map_nil,
    CoreCallableCompositionalResourceStorage.realize,List.nil_append] using lower

def originalGraphPrefix : CheckedGraphPrefix CoreCallableCompositionalResourceRoot.graph originalPath
    Original.api Original.policy Original.declarations [] [] [] .none [] :=
  ⟨originalPrefix,CoreCallableCompositionalResourceRoot.original_graph_shape,
    CoreCallableCompositionalResourceRoot.original_graph_translation⟩

theorem original_graph_prefix_executed :
    produce_graph_prefix CoreCallableCompositionalResourceRoot.graph originalPath
      Original.api Original.policy Original.declarations [] [] [] .none [] = .ok originalGraphPrefix := by
  unfold produce_graph_prefix
  split
  · rename_i failed
    have bad := failed.symm.trans CoreCallableCompositionalResourceRoot.original_graph_shape
    cases bad
  · split
    · rename_i failed
      have bad := failed.symm.trans CoreCallableCompositionalResourceRoot.original_graph_translation
      cases bad
    · rename_i actual translated
      have same := Except.ok.inj (translated.symm.trans CoreCallableCompositionalResourceRoot.original_graph_translation)
      subst actual
      simp only [CoreCallableChecks.codeEq_refl]
      rw [prefix_executed]
      rfl

theorem original_resource_site : ∃ node, CoreCallableCompositionalResourceRoot.graph.node 21 = some node ∧
    node.kind = .resource 3 ⟨9,.reference (.bound 3)⟩ 3 20 := ⟨_,rfl,rfl⟩

theorem wrong_root_rejected : produce_graph_prefix CoreCallableCompositionalResourceRoot.graph
    (Prefix.here (entries := Original.entries) (owners := Original.globals.owners) (root := .unit))
    Original.api Original.policy Original.declarations [] [] [] .none [] = .error .code := rfl

abbrev alias_code := CoreCallableCompositionalResourceStorage.Probes.AliasRetention.code

theorem alias_source_still_accepted : CoreCallableCompositionalResourceOpening.resourceCheck
    CoreCallableCompositionalResourceStorage.Probes.AliasRetention.original
    CoreCallableCompositionalResourceStorage.Probes.AliasRetention.body Original.api 3 [] [] [] [(7,[])] [] = true :=
  CoreCallableCompositionalResourceStorage.Probes.AliasRetention.source_gate_accepts

theorem alias_outside_rejected : CoreCallableCompositionalResourceStorage.opening
    Original.api 3 [] CoreCallableCompositionalResourceStorage.Probes.storageBindings alias_code
    CoreCallableCompositionalResourceStorage.Probes.AliasRetention.recipe [] = none :=
  CoreCallableCompositionalResourceStorage.Probes.AliasRetention.outside_storage_rejects

theorem original_graph_resource_executed : ∃ composite,
    produce_graph_opened originalGraphPrefix Original.annotation Original.body Original.initialRecipe Original.bodyRecipe [] [] = .ok composite := by
  obtain ⟨opened,accepted⟩ := resource_executed
  exact produce_graph_opened_success accepted

theorem original_graph_captured_reader : ∃ composite,
    produce_graph_opened originalGraphPrefix Original.annotation Original.body Original.initialRecipe Original.bodyRecipe [] [] = .ok composite ∧
    ∃ reader : ReaderPath composite.resource, ∃ family : ReaderFamily changedReader,
      Authenticated Original.globals.registry [] (family.whole (allowed := [.cell 1]) (scope := .none)) [(7,[])] [1] ∧
      CallableContracts.Derives Original.declarations
        (CoreCallableReturnStorageProducer.environment [(7,.storage [])]) [1] .none
        (.lambda 10 changedReader) (.function [1,1] (.storage []) (.storage [])) ∧
      ∃ current : Current reader.path 1 (by simp), ∃ handle : CapturedHandle reader.path 1 (by simp),
      ∃ replacement : IndexedSource Original.globals.registry [] Original.globals.owners [1] [.cell 1] .none
        (CoreCallableStaticProducer.environment [(7,.integer)]) (.resourceRef (.activation 1)) (.reference 1)
        [] (.request [] []) .pure SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Rows.pure,
      CoreCallableCapturedLambdaConstructor.Receipt current.source replacement structural_policy_stable handle.closed changedReader family := by
  obtain ⟨composite,accepted⟩ := original_graph_resource_executed
  obtain ⟨reader,_⟩ := connected_reader composite.resource
  obtain ⟨family,auth,lower,receipts⟩ := original_closed_reader reader
  exact ⟨composite,accepted,reader,family,auth,lower,receipts⟩

theorem shadow_return_rejected : CoreCallableCompositionalResourceStorage.opening Original.api 3 [1]
    [(7,.storage [1]),(7,.storage [])] (.variable 7) .variable [] = none :=
  CoreCallableCompositionalResourceStorage.Probes.shadowed_outside_return_rejected

theorem opaque_domain_rejected : CoreCallableCompositionalResourceStorage.check Original.api 3 []
    (CoreCallableCompositionalResourceStorage.original [(2,.function [] (.pair (.storage []) (.storage [])) (.storage [])),(1,.storage [])])
    (.app (.variable 2) (.variable 1)) (.app .variable .variable) = none :=
  CoreCallableCompositionalResourceStorage.Probes.opaque_application_domain_rejected

#print axioms prefix_executed
#print axioms prefix_full_maps
#print axioms resource_executed
#print axioms connected_reader
#print axioms reader_checked
#print axioms reader_full_storage
#print axioms reader_current_all_fresh
#print axioms handle_executed
#print axioms connected_higher
#print axioms higher_current_all_fresh
#print axioms original_closed_reader
#print axioms original_graph_prefix_executed
#print axioms original_resource_site
#print axioms wrong_root_rejected
#print axioms alias_source_still_accepted
#print axioms alias_outside_rejected
#print axioms original_graph_resource_executed
#print axioms original_graph_captured_reader
#print axioms shadow_return_rejected
#print axioms opaque_domain_rejected
end Ash.OneShot.CoreCallableComposedResourceOrigins.Probes
