import CoreCallableStaticProducer
import CoreCallableFiniteRegistryCompatibility
namespace Ash.OneShot.CoreCallableFiniteRegistryBridge
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract)
open CoreCallableContractAdmission CoreCallableReceiverRefinement
open CoreCallableStaticProducer (StaticTree)
open CoreCallableFiniteCellRegistry (CellApi)
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

/-- Limited to StaticTree, which has no handler constructor. Full
original code, contracts, dependencies, plans and rows remain exact indices. -/
theorem transfer_tree
    {source : IndexedSource (CoreCallableStaticProducer.registry entries policy) outward owners world allowed scope
      environment code contract demand requirements plan rows}
    (tree : StaticTree (CoreCallableStaticProducer.registry entries policy) outward source)
    (accepted : CoreCallableFiniteRegistryCompatibility.compatible api entries = true) :
    ∃ next : IndexedSource (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward owners world allowed scope
      environment code contract demand requirements plan rows,
      StaticTree (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward next := by
  induction tree with
  | unit => exact ⟨.unit,.unit⟩
  | boolean => exact ⟨.boolean,.boolean⟩
  | integer => exact ⟨.integer,.integer⟩
  | reference => exact ⟨.reference (by assumption),.reference (issued := by assumption)⟩
  | «variable» => exact ⟨.variable (by assumption) (by assumption),.variable (known := by assumption) (formed := by assumption)⟩
  | pair left right ihL ihR =>
      obtain ⟨l,lt⟩ := ihL
      obtain ⟨r,rt⟩ := ihR
      exact ⟨.pair l r,.pair lt rt⟩
  | bind initial body ihI ihB =>
      obtain ⟨i,it⟩ := ihI
      obtain ⟨b,bt⟩ := ihB
      exact ⟨.bind i b,.bind it bt⟩
  | app function argument ihF ihA =>
      obtain ⟨f,ft⟩ := ihF
      obtain ⟨a,argTree⟩ := ihA
      exact ⟨.app f a (by assumption) (by assumption),
        .app (admitted := by assumption) (publicCertified := by assumption) ft argTree⟩
  | resume operand ih =>
      obtain ⟨v,vt⟩ := ih
      exact ⟨.resume (by assumption) (by assumption) (by assumption) v (by assumption) (by assumption),
        .resume (known := by assumption) (resolved := by assumption) (permission := by assumption)
          (admitted := by assumption) (formed := by assumption) vt⟩
  | discard known resolved permission unprotected admitted =>
      exact ⟨.discard (registry := CoreCallableFiniteCellRegistry.registry (some api) entries policy) known resolved permission unprotected admitted,
        .discard (registry := CoreCallableFiniteCellRegistry.registry (some api) entries policy) known resolved permission unprotected admitted⟩
  | cleanup callback body ihC ihB =>
      obtain ⟨c,ct⟩ := ihC
      obtain ⟨b,bt⟩ := ihB
      exact ⟨.cleanup c b (by assumption) (by assumption),
        .cleanup (admitted := by assumption) (publicCertified := by assumption) ct bt⟩
  | perform operand ih =>
      obtain ⟨v,vt⟩ := ih
      have mapped := CoreCallableFiniteRegistryCompatibility.selected_lookup_preserved (policy := policy) accepted (by assumption)
      exact ⟨.perform mapped (by assumption) v (by assumption),
        .perform (known := mapped) (admitted := by assumption) (formed := by assumption) vt⟩
  | branch condition yes no ihC ihY ihN =>
      obtain ⟨c,ct⟩ := ihC
      obtain ⟨y,yt⟩ := ihY
      obtain ⟨n,nt⟩ := ihN
      exact ⟨.branch c y n (by assumption),.branch (sameDemand := by assumption) ct yt nt⟩
  | lambda body ih =>
      obtain ⟨b,bt⟩ := ih
      exact ⟨.lambda b (by assumption) (by assumption) (by assumption) (by assumption) (by assumption),
        .lambda (refinement := by assumption) (bodyOutward := by assumption) (latentBound := by assumption)
          (publicCertified := by assumption) (formed := by assumption) bt⟩
  | resource initial body ihI ihB =>
      obtain ⟨i,it⟩ := ihI
      let sources := fun identity fresh =>
        (ihB identity fresh).elim (fun next _tree => next)
      have trees : ∀ identity fresh, StaticTree _ outward (sources identity fresh) := by
        intro identity fresh
        obtain ⟨next,tree⟩ := ihB identity fresh
        exact tree
      exact ⟨.resource i sources (by assumption) (by assumption) (by assumption) (by assumption),
        .resource (formed := by assumption) (effectsBound := by assumption)
          (admitted := by assumption) (hidden := by assumption) it trees⟩
  | receiverLambda body refinement ih =>
      obtain ⟨b,bt⟩ := ih
      exact ⟨.receiverLambda (fun _ call => b.world_weaken call.worldExtended)
        (by assumption) (by assumption) (by assumption) (by assumption),
        .receiverLambda (bodyOutward := by assumption) (latentBound := by assumption)
          (publicCertified := by assumption) (formed := by assumption) bt refinement⟩

/-- Same-index constructive output, not a Source/Auth field in annotation. -/
def Rechecked (api : CellApi) (entries : CoreCallableStaticProducer.OperationEntries)
    (policy : Syntax.TicketPolicy) (outward : List Instance) (owners : CoreCallableContractRegistries.Owners)
    (world : List Nat) (allowed : List Instance) (scope : Execution.Scope)
    (bindings : CoreCallableStaticProducer.Bindings) (code : Code) (contract : Contract)
    (demand : List Nat) (requirements : RecursiveRequirements.Requirements demand)
    (plan : SourceDeclarationPlans.Plan dependencies)
    (rows : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Rows (SourcePlanSignatures.signature plan))
    (lexical : LexicalBounds) (receiver : List Nat) : Prop :=
  ∃ source : IndexedSource (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward owners world allowed scope
      (CoreCallableStaticProducer.environment bindings) code contract demand requirements plan rows,
    StaticTree (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward source ∧
    Authenticated (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward source lexical receiver ∧ receiver ⊆ world

 theorem produced_rechecked
    (original : CoreCallableStaticProducer.Result entries policy outward owners world allowed scope bindings code contract demand requirements plan rows lexical receiver)
    (compatible : CoreCallableFiniteRegistryCompatibility.compatible api entries = true)
    (known : CoreCallableGraphAnnotationChecks.knownB lexical code.dependencies = true)
    (bounds : CoreCallableGraphAnnotationChecks.subsetB (ScopedPorts.Support.evaluate lexical.environment code.dependencies) receiver = true) :
    Rechecked api entries policy outward owners world allowed scope bindings code contract demand requirements plan rows lexical receiver := by
  obtain ⟨next,tree⟩ := transfer_tree original.tree compatible
  exact ⟨next,tree,tree.authenticate_world (List.Subset.refl _)
    (CoreCallableGraphAnnotationChecks.knownB_sound known)
    (SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mpr
      (CoreCallableGraphAnnotationChecks.subsetB_sound bounds)),original.receivingIssued⟩

inductive Error where
  | incompatibleRegistry
  | originalCheck : CoreCallableStaticProducer.Error → Error
  | originalSupport
  | originalLexical
  deriving Repr

/-- Execute the original fourteen constructor checks, then checked finite
selected-lookup transport. There is no arbitrary registry substitution. -/
def recheck
    (annotation : CoreCallableStaticProducer.Annotation entries owners bindings code contract demand requirements plan rows)
    (api : CellApi) (policy : Syntax.TicketPolicy) (outward : List Instance) (world : List Nat)
    (allowed : List Instance) (scope : Execution.Scope) (lexical : LexicalBounds) (receiver : List Nat) :
    Except Error (PLift (Rechecked api entries policy outward owners world allowed scope bindings code contract demand requirements plan rows lexical receiver)) := do
  if compatible : CoreCallableFiniteRegistryCompatibility.compatible api entries = true then
    match _original : CoreCallableStaticProducer.check annotation policy outward world allowed scope lexical receiver with
    | .error error => .error (.originalCheck error)
    | .ok result =>
      if known : CoreCallableGraphAnnotationChecks.knownB lexical code.dependencies = true then
        if bounds : CoreCallableGraphAnnotationChecks.subsetB (ScopedPorts.Support.evaluate lexical.environment code.dependencies) receiver = true then
          .ok ⟨produced_rechecked result compatible known bounds⟩
        else .error .originalSupport
      else .error .originalLexical
  else .error .incompatibleRegistry

 theorem recheck_success
    {annotation : CoreCallableStaticProducer.Annotation entries owners bindings code contract demand requirements plan rows}
    (_accepted : recheck annotation api policy outward world allowed scope lexical receiver = .ok receipt) :
    Rechecked api entries policy outward owners world allowed scope bindings code contract demand requirements plan rows lexical receiver := receipt.down

/-- Run the single original constructor checker at the checked schema backend
and project its SAME computed source. This path performs no tree transfer. -/
def recheck_cell
    (annotation : CoreCallableStaticProducer.Annotation entries owners bindings code contract demand requirements plan rows)
    (api : CellApi) (policy : Syntax.TicketPolicy) (outward : List Instance) (world : List Nat)
    (allowed : List Instance) (scope : Execution.Scope) (lexical : LexicalBounds) (receiver : List Nat) :
    Except Error (PLift (Rechecked api entries policy outward owners world allowed scope bindings code contract demand requirements plan rows lexical receiver)) :=
  match CoreCallableStaticProducer.check_cell annotation api policy outward world allowed scope lexical receiver with
  | .error .incompatibleRegistry => .error .incompatibleRegistry
  | .error (.originalCheck error) => .error (.originalCheck error)
  | .ok actual => .ok ⟨⟨actual.source,actual.tree,actual.authenticated,actual.receivingIssued⟩⟩

/-- A successful direct gate exposes only its actually returned judgment. -/
theorem recheck_cell_success
    {annotation : CoreCallableStaticProducer.Annotation entries owners bindings code contract demand requirements plan rows}
    (_accepted : recheck_cell annotation api policy outward world allowed scope lexical receiver = .ok receipt) :
    Rechecked api entries policy outward owners world allowed scope bindings code contract demand requirements plan rows lexical receiver := receipt.down


#print axioms transfer_tree
#print axioms produced_rechecked
#print axioms recheck_success
#print axioms recheck_cell_success
end Ash.OneShot.CoreCallableFiniteRegistryBridge
