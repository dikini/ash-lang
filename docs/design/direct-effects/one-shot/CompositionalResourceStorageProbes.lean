import CoreCallableCompositionalResourceStorage
import CoreCallableCompositionalResourceRoot
namespace Ash.OneShot.CoreCallableCompositionalResourceStorage.Probes
open ScopedExpressions ScopedExecution
open CoreCallableCompositionalResourceStorage
namespace Original
abbrev body := CoreCallableCompositionalResourceRoot.body
abbrev code := CoreCallableCompositionalResourceRoot.codeOf body
abbrev entries := CoreCallableCompositionalResourceRoot.entries
abbrev globals := CoreCallableCompositionalResourceRoot.globals
abbrev policy := CoreCallableCompositionalResourceRoot.policy
abbrev root := CoreCallableCompositionalResourceRoot.rootCode
abbrev initializer := CoreCallableCompositionalResourceRoot.resourceInitializer
abbrev annotation := CoreCallableCompositionalResourceRoot.initializerAnnotation
end Original
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def api := CoreCallableFiniteCellRegistry.original
def declarations : Instantiation.DeclarationRegistry := fun _ => none
def storageBindings : CoreCallableReturnStorageProducer.Bindings := [(7,.storage [])]
def bodyRecipe : Recipe := .bind .leaf
  (.bind (.lambda (.storage []) (.cell .variable))
    (.bind (.lambda (.slot 12) (.app .variable .leaf))
      (.bind (.app .variable .variable) (.branch .leaf .variable .variable))))
def initializerRecipe : CoreCallableStorageRecipes.Recipe :=
  .node none [.node (some (.storage [])) [],.node none []]
def outerAnnotation : CoreCallableReturnStorageProducer.Annotation := .node (some (.storage [])) []
def records : List CoreCallableReturnStorageProducer.BindingAnnotation :=
  [⟨7,.integer 17,outerAnnotation,.storage [],[]⟩]

theorem original_storage_initializer_checked :
    CoreCallableReturnStorageProducer.check [] (.integer 17) outerAnnotation = some (.storage []) := by simp [CoreCallableReturnStorageProducer.check,outerAnnotation,CoreCallableReturnStorageProducer.captureCheck,Code.dependencies]

theorem original_paired_prefix : CoreCallablePairedOrigin.Origins Original.globals.registry declarations [] Original.globals.owners [] [] .none []
    Original.root (.resource 3 Original.initializer Original.code)
    [(7,.integer)] storageBindings [(7,[])] records := by
  obtain ⟨receipt,accepted⟩ := CoreCallableGeneralResourceInitialRoot.original_initializer_checked
  obtain ⟨rich,_tree,authenticated,_issued⟩ := CoreCallableFiniteRegistryBridge.recheck_success accepted
  exact .bind .initial rich authenticated
    (CoreCallableReturnStorageProducer.check_sound original_storage_initializer_checked) (List.nil_subset _)

set_option linter.unusedSimpArgs false in
theorem body_checked : ∃ produced, check api 3 [] (original storageBindings) Original.code bodyRecipe = some ⟨Tree.storage [],produced⟩ := by
  dsimp only [Original.code,CoreCallableCompositionalResourceRoot.codeOf,
    CoreCallableCompositionalResourceRoot.body,CoreCallableCompositionalResourceRoot.reader,
    CoreCallableCompositionalResourceRoot.higherOrder,CoreCallableCompositionalResourceRoot.applyFormal,
    CoreCallableCompositionalResourceRoot.actualCall,CoreCallableCompositionalResourceRoot.choice,
    CoreCallableCompositionalResourceRoot.condition,CoreCallableCompositionalResourceRoot.returned,
    bodyRecipe,storageBindings,api]
  repeat' (first
    | dsimp [original,Tree.original,lookup,Tree.valid,Atom.valid,template,template.bounds,
        captures,collect,Tree.storageOf,nameAtom,Code.dependencies,Code.freeNames,
        CoreCallableFiniteCellRegistry.CellApi.check,CoreCallableFiniteCellRegistry.original,
        Syntax.without,effectAtoms,Instantiation.Effect.resources,Instantiation.Effect.freeNames,
        Instantiation.ResourceName.freeNames]
    | simp only [CoreCallableCompositionalResourceStorage.check])
  exact ⟨_,rfl⟩

theorem body_opening_checked : ∃ receipt, opening api 3 [] storageBindings Original.code bodyRecipe [] = some receipt := by
  obtain ⟨produced,accepted⟩ := body_checked
  unfold opening
  split
  · rename_i failed
    rw [failed] at accepted
    contradiction
  · rename_i result proof checked
    have equal := Option.some.inj (checked.symm.trans accepted)
    cases equal
    exact ⟨_,rfl⟩

theorem same_body_all_fresh (identity : Nat) :
    CallableContracts.Derives declarations (CoreCallableReturnStorageProducer.environment storageBindings)
      [identity] .none (Original.code.instantiate (Instantiation.Environment.empty.bind 3 identity)) (.storage []) := by
  obtain ⟨produced,accepted⟩ := body_checked
  simpa [realize_original,Tree.value] using (produced.derive (declarations := declarations) (identity := identity) (ticket := .none))


set_option linter.unusedSimpArgs false in
theorem original_resource_initializer_checked :
    CoreCallableStorageRecipes.check storageBindings Instantiation.Environment.empty Original.initializer initializerRecipe = some (.storage []) := by
  dsimp only [Original.initializer,CoreCallableGeneralResourceInitialRoot.resourceInitializer,initializerRecipe]
  simp [CoreCallableStorageRecipes.check,CoreCallableStorageRecipes.specialize,CoreCallableStorageRecipes.specializeList,CoreCallableCompositionalResourceRoot.resourceInitializer,CoreCallableGeneralResourceInitialRoot.resourceInitializer,CoreCallableStorageRecipes.contract,CoreCallableStorageRecipes.bound,
    storageBindings,CoreCallableReturnStorageProducer.check,CoreCallableReturnStorageProducer.lookup,
    CoreCallableReturnStorageProducer.extend,CoreCallableReturnStorageProducer.captureCheck,Code.dependencies]

theorem combined_checked : ∃ receipt,
    check_composed (api := api) original_paired_prefix Original.annotation Original.body initializerRecipe bodyRecipe [] [] = .ok receipt := by
  obtain ⟨source,sourceAccepted⟩ := CoreCallableCompositionalResourceRoot.compositional_checked
  obtain ⟨opened,openingAccepted⟩ := body_opening_checked
  exact check_composed_accepted sourceAccepted original_resource_initializer_checked openingAccepted (List.Subset.refl _)

theorem body_opening_result (receipt : Opening api 3 [] storageBindings Original.code bodyRecipe []) : receipt.result = .storage [] := by
  obtain ⟨produced,accepted⟩ := body_checked
  exact congrArg Sigma.fst (Option.some.inj (receipt.accepted.symm.trans accepted))

-- The lower judgment is on the SAME original resource, full old map and initializer.
theorem combined_resource_storage :
    CallableContracts.Derives declarations (CoreCallableReturnStorageProducer.environment storageBindings) [] .none
      (.resource 3 Original.initializer Original.code) (.storage []) := by
  obtain ⟨receipt,_accepted⟩ := combined_checked
  simpa [body_opening_result receipt.opening,Tree.value] using receipt.resource

theorem returned_fresh_excluded (identity : Nat) : ∃ receipt,
    check_composed (api := api) original_paired_prefix Original.annotation Original.body initializerRecipe bodyRecipe [] [] = .ok receipt ∧
      identity ∉ (receipt.opening.result.value 0).storageOf := by
  obtain ⟨receipt,accepted⟩ := combined_checked
  exact ⟨receipt,accepted,receipt.fresh_excluded (by simp)⟩

theorem original_paired_maps_preserved : ∃ receipt,
    check_composed (api := api) original_paired_prefix Original.annotation Original.body initializerRecipe bodyRecipe [] [] = .ok receipt ∧
      receipt.paired = original_paired_prefix := by
  obtain ⟨receipt,accepted⟩ := combined_checked
  exact ⟨receipt,accepted,receipt.pairedSame⟩

-- Exact actual captures: the lexical handle and the bound read both carry fresh.
theorem reader_actual_capture : captures [(9,.storage [.fresh]),(7,.storage [])] 3
    (.lambda 10 (.perform (.cell (.bound 3)) 0 (.variable 9))) = some [.fresh,.fresh] := rfl

namespace AliasRetention
open CoreCallableCompositionalResourceBody
abbrev original : CoreCallableStaticProducer.Bindings := [(7,.integer)]
abbrev outside : CoreCallableCompositionalResourceBody.Context := [(7,.old (.slot 0))]
abbrev handles : CoreCallableCompositionalResourceBody.Context := (9,.old (.reference (.bound 3)))::outside
def aliasBody := Body.bind (parameter := 21)
  (Body.variable (original := original) (context := (10,.old .unit)::handles) (Ref.tail Ref.head))
  (Body.embedded (context := (21,.old (.reference (.bound 3)))::(10,.old .unit)::handles)
    (CoreCallableFiniteResourceTemplate.Body.integer (context := []) 42))
def closure := Body.lambda (parameter := 10) (.old .unit) [] aliasBody
def body := Body.bind (parameter := 9)
  (Body.embedded (original := original) (context := outside)
    (CoreCallableFiniteResourceTemplate.Body.reference (context := [(7,.slot 0)]) (.bound 3))) closure

theorem source_gate_accepts : CoreCallableCompositionalResourceOpening.resourceCheck original body api 3 [] [] [] [(7,[])] [] = true := rfl

def code : Code := .bind 9 (.resourceRef (.bound 3)) (.lambda 10 (.bind 21 (.variable 9) (.integer 42)))
def recipe : Recipe := .bind .leaf (.lambda (.storage []) (.bind .variable .leaf))
set_option linter.unusedSimpArgs false in
theorem checked_captures_handle : ∃ produced,
    check api 3 [] (CoreCallableCompositionalResourceStorage.original storageBindings) code recipe =
      some ⟨Tree.function [.fresh] (.storage []) (.storage []),produced⟩ := by
  dsimp only [code,recipe,api,storageBindings]
  repeat' (first
    | dsimp [CoreCallableCompositionalResourceStorage.original,Tree.original,lookup,Tree.valid,Atom.valid,template,template.bounds,
        captures,collect,Tree.storageOf,nameAtom,Code.dependencies,Code.freeNames,
        CoreCallableFiniteCellRegistry.CellApi.check,CoreCallableFiniteCellRegistry.original,
        Syntax.without,effectAtoms,Instantiation.Effect.resources,Instantiation.Effect.freeNames,
        Instantiation.ResourceName.freeNames]
    | simp only [CoreCallableCompositionalResourceStorage.check])
  exact ⟨_,rfl⟩

theorem outside_storage_rejects : opening api 3 [] storageBindings code recipe [] = none := by
  obtain ⟨produced,accepted⟩ := checked_captures_handle
  unfold opening
  split
  · rfl
  · rename_i result proof checked
    have equal := Option.some.inj (checked.symm.trans accepted)
    cases equal
    rfl
end AliasRetention

-- Nearest lookup retains the new full slot, so older shadowed support cannot authorize return.
theorem shadowed_full_slot : lookup [(7,.storage [.fresh]),(7,.storage [])] 7 = some (.storage [.fresh]) := rfl

theorem full_domain_difference (identity : Nat) :
    Tree.value identity (.function [] (.storage []) (.storage [])) ≠
      Tree.value identity (.function [] (.pair (.storage []) (.storage [])) (.storage [])) := by
  simp [Tree.value]

theorem alias_same_source_code : CoreCallableCompositionalResourceRoot.codeOf AliasRetention.body = AliasRetention.code := rfl

theorem same_original_graph : CoreTranslation.translate CoreCallableCompositionalResourceRoot.graph = .ok Original.root :=
  CoreCallableCompositionalResourceRoot.original_graph_translation

-- Same erased capture support is insufficient: application compares the entire opaque domain.
set_option linter.unusedSimpArgs false in
theorem opaque_application_domain_rejected :
    check api 3 [] (original [(2,.function [] (.pair (.storage []) (.storage [])) (.storage [])),(1,.storage [])])
      (.app (.variable 2) (.variable 1)) (.app .variable .variable) = none := by
  repeat' (first
    | dsimp [api,original,Tree.original,lookup,Tree.valid,Atom.valid]
    | simp only [CoreCallableCompositionalResourceStorage.check])
  rfl

set_option linter.unusedSimpArgs false in
theorem shadowed_outside_return_rejected : opening api 3 [1] [(7,.storage [1]),(7,.storage [])] (.variable 7) .variable [] = none := by
  unfold opening
  split
  · rfl
  · rename_i result proof accepted
    have concrete : check api 3 [1] (original [(7,.storage [1]),(7,.storage [])]) (.variable 7) .variable = some ⟨Tree.storage [.old 1],Produced.variable rfl rfl⟩ := by
      simp only [CoreCallableCompositionalResourceStorage.check]
      exact rfl
    have equal := Option.some.inj (accepted.symm.trans concrete)
    cases equal
    rfl

#print axioms alias_same_source_code
#print axioms same_original_graph
#print axioms opaque_application_domain_rejected
#print axioms shadowed_outside_return_rejected

#print axioms AliasRetention.source_gate_accepts
#print axioms AliasRetention.checked_captures_handle
#print axioms AliasRetention.outside_storage_rejects
#print axioms shadowed_full_slot
#print axioms full_domain_difference

#print axioms original_resource_initializer_checked
#print axioms combined_checked
#print axioms body_opening_result
#print axioms returned_fresh_excluded
#print axioms combined_resource_storage
#print axioms original_paired_maps_preserved
#print axioms reader_actual_capture

#print axioms original_storage_initializer_checked
#print axioms original_paired_prefix
#print axioms body_checked
#print axioms body_opening_checked
#print axioms same_body_all_fresh

end Ash.OneShot.CoreCallableCompositionalResourceStorage.Probes
