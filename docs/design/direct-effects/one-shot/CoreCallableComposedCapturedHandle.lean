import CoreCallableComposedResourceOrigins
namespace Ash.OneShot.CoreCallableComposedCapturedHandle
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract)
open CoreCallableContractAdmission CoreCallableReceiverRefinement
open CoreCallableComposedResourceOrigins
open CoreCallableCompositionalResourceBody
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

section
variable {prior : CheckedOriginalPrefix (originalPath : Prefix entries owners root (.resource binder initial code) original)
  api policy declarations outward world allowed scope receiver}
variable {annotation : CoreCallableStaticProducer.Annotation entries owners original initial .integer initialDemand initialReq initialPlan initialRows}
variable {body : Body original rootContext code rootPattern rootChecking rootNeeds}
variable {opened : ResourceOpened prior annotation body initialRecipe bodyRecipe residual bound}
variable {current : Body original ((name,.old (.reference (.bound binder)))::context)
  currentCode currentPattern currentChecking currentNeeds}
variable {produced : CoreCallableCompositionalResourceStorage.Produced api binder world
  ((name,.storage [.fresh])::storage) currentCode stored}

/-- The closed reference is checked at the exact selected original handle slot.
This receipt produces a static closed value, not initializer evaluation or
Core acquisition. Both executed checks retain the entire outside maps. -/
structure CapturedHandle
    (path : OpenedBind opened current produced recipe (name::names))
    (identity : Nat) (fresh : identity ∉ world) : Prop where
  rechecked : CoreCallableFiniteRegistryBridge.Rechecked api entries policy outward owners
    (world ++ [identity]) (.cell identity::residual) scope
    (bindings original identity context) (.resourceRef (.activation identity)) (.reference identity)
    [] (.request [] []) .pure Rows.pure (lexicalAfter prior.lexical (identity::receiver) names) (identity::receiver)
  richAccepted : ∃ receipt,
    CoreCallableFiniteRegistryBridge.recheck
      (CoreCallableStaticProducer.Annotation.reference (bindings := bindings original identity context) (entries := entries) (owners := owners) identity)
      api policy outward (world ++ [identity]) (.cell identity::residual) scope
      (lexicalAfter prior.lexical (identity::receiver) names) (identity::receiver) = .ok receipt
  storageAccepted : CoreCallableReturnStorageProducer.check
    (CoreCallableCompositionalResourceStorage.realize identity storage)
    (.resourceRef (.activation identity)) (.node (some (.storage [identity])) []) = some (.storage [identity])
  closed : ClosedValue (.resourceRef (.activation identity))

inductive Error where
  | rich : CoreCallableFiniteRegistryBridge.Error → Error
  | storage

def capture_handle
    (path : OpenedBind opened current produced recipe (name::names)) (identity : Nat) (fresh : identity ∉ world) :
    Except Error (PLift (CapturedHandle path identity fresh)) :=
  match accepted : CoreCallableFiniteRegistryBridge.recheck
    (CoreCallableStaticProducer.Annotation.reference (bindings := bindings original identity context) (entries := entries) (owners := owners) identity)
    api policy outward (world ++ [identity]) (.cell identity::residual) scope
    (lexicalAfter prior.lexical (identity::receiver) names) (identity::receiver) with
  | .error error => .error (.rich error)
  | .ok receipt =>
    match checked : CoreCallableReturnStorageProducer.check
      (CoreCallableCompositionalResourceStorage.realize identity storage)
      (.resourceRef (.activation identity)) (.node (some (.storage [identity])) []) with
    | none => .error .storage
    | some result =>
      if same : result = .storage [identity] then
        .ok ⟨⟨receipt.down,⟨receipt,accepted⟩,by simpa only [same] using checked,
          by simp [ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Code.dependencies,Instantiation.ResourceName.freeNames]⟩⟩
      else .error .storage

 theorem CapturedHandle.lower
    {path : OpenedBind opened current produced recipe (name::names)}
    (handle : CapturedHandle path identity fresh) :
    CallableContracts.Derives declarations
      (CoreCallableReturnStorageProducer.environment (CoreCallableCompositionalResourceStorage.realize identity storage))
      (world ++ [identity]) .none (.resourceRef (.activation identity)) (.storage [identity]) :=
  CoreCallableReturnStorageProducer.check_sound handle.storageAccepted

 theorem capture_handle_success
    {identity : Nat} {fresh : identity ∉ world}
    {receipt : PLift (CoreCallableFiniteRegistryBridge.Rechecked api entries policy outward owners
      (world ++ [identity]) (.cell identity::residual) scope (bindings original identity context)
      (.resourceRef (.activation identity)) (.reference identity) [] (.request [] []) .pure Rows.pure
      (lexicalAfter prior.lexical (identity::receiver) names) (identity::receiver))}
    {path : OpenedBind opened current produced recipe (name::names)}
    (accepted : CoreCallableFiniteRegistryBridge.recheck
      (CoreCallableStaticProducer.Annotation.reference (bindings := bindings original identity context) (entries := entries) (owners := owners) identity)
      api policy outward (world ++ [identity]) (.cell identity::residual) scope
      (lexicalAfter prior.lexical (identity::receiver) names) (identity::receiver) = .ok receipt)
    (stored : CoreCallableReturnStorageProducer.check (CoreCallableCompositionalResourceStorage.realize identity storage)
      (.resourceRef (.activation identity)) (.node (some (.storage [identity])) []) = some (.storage [identity])) :
    ∃ output, capture_handle path identity fresh = .ok output := by
  unfold capture_handle
  split
  · rename_i failed
    rw [failed] at accepted
    contradiction
  · split
    · rename_i failed
      rw [failed] at stored
      contradiction
    · rename_i result checked
      have same := Option.some.inj (checked.symm.trans stored)
      subst result
      simp
      exact ⟨⟨⟨receipt.down,⟨receipt,accepted⟩,stored,
        by simp [ClosedValue,Code.IsValue,Code.ResourceClosed,Code.freeNames,Code.dependencies,Instantiation.ResourceName.freeNames]⟩⟩,True.intro⟩

end

/-- The installed structural declaration policy already proves signature
transport; this is derived policy evidence, not a caller's future check. -/
theorem structural_policy_stable : SubstitutionPolicyStable outward :=
  fun accepted same => SourceScheduledCleanupInterfaces.Lexical.Recursive.ClauseDeclarations.signature_congr accepted same

section Reader
variable {prior : CheckedOriginalPrefix (originalPath : Prefix entries owners root (.resource binder initial code) original)
  api policy declarations outward world allowed scope receiver}
variable {annotation : CoreCallableStaticProducer.Annotation entries owners original initial .integer initialDemand initialReq initialPlan initialRows}
variable {body : Body original rootContext code rootPattern rootChecking rootNeeds}
variable {opened : ResourceOpened prior annotation body initialRecipe bodyRecipe residual bound}
variable {current : Body original ((name,.old (.reference (.bound binder)))::context)
  (.lambda formal readerCode) (.function input output requests latent checking) .pure .empty}
variable {produced : CoreCallableCompositionalResourceStorage.Produced api binder world
  ((name,.storage [.fresh])::storage) (.lambda formal readerCode) stored}
variable {path : OpenedBind opened current produced recipe (name::names)}
variable {identity : Nat} {fresh : identity ∉ world}

/-- Preserve the original entire public contract and its constructor-origin
private family. Reconstruction computes every private member at its restored
lexical/call point; lower substitution uses the SAME full storage map. -/
theorem close_reader_handle
    (receipt : Current path identity fresh)
    (handle : CapturedHandle path identity fresh) :
    ∃ nextCode, ∃ family : CoreCallableCapturedLambdaConstructor.Family
        (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward owners
        (world ++ [identity]) (CoreCallableStaticProducer.environment (bindings original identity context)) formal nextCode
        (input.value original identity) (output.value original identity)
        (requests.map (EffectName.value identity)) (latent.map (RequestName.value identity))
        (checking.plan identity) (checking.rows identity),
      ∃ replacement : IndexedSource (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward owners
        (world ++ [identity]) (.cell identity::residual) scope
        (CoreCallableStaticProducer.environment (bindings original identity context))
        (.resourceRef (.activation identity)) (.reference identity) [] (.request [] []) .pure Rows.pure,
      CoreCallableCapturedLambdaConstructor.Receipt receipt.source replacement structural_policy_stable handle.closed nextCode family ∧
      Code.lambda formal nextCode =
        (Code.lambda formal (readerCode.instantiate (Instantiation.Environment.empty.bind binder identity))).subst name (.resourceRef (.activation identity)) ∧
      Authenticated (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward
        (family.whole (allowed := .cell identity::residual) (scope := scope))
        (lexicalAfter prior.lexical (identity::receiver) names) (identity::receiver) ∧
      CallableContracts.Derives declarations
        (CoreCallableReturnStorageProducer.environment (CoreCallableCompositionalResourceStorage.realize identity storage))
        (world ++ [identity]) .none (Code.lambda formal nextCode) (stored.value identity) := by
  obtain ⟨replacement,_,auth,_⟩ := handle.rechecked
  have current := receipt.authenticated
  have lower := receipt.storage
  have actual : Syntax.resourceDependencies (Code.resourceRef (.activation identity)).dependencies ⊆ identity::receiver := by simp [Code.dependencies,Syntax.resourceDependencies]
  obtain ⟨nextCode,family,origin,same,authenticated⟩ :=
    CoreCallableCapturedLambdaConstructor.reconstruct current structural_policy_stable replacement handle.closed actual auth
  have changed := CallableContracts.substitution lower handle.lower handle.closed
  refine ⟨nextCode,family,replacement,origin,same,authenticated,?_⟩
  rw [same]
  exact changed

end Reader
#print axioms capture_handle
#print axioms CapturedHandle.lower
#print axioms capture_handle_success
#print axioms structural_policy_stable
#print axioms close_reader_handle
end Ash.OneShot.CoreCallableComposedCapturedHandle
