import CoreCallableResourceIndexData
import CoreCallableFiniteCellRegistry
import CoreCallableStaticTreeCarrier

/-! Finite typed instructions for the SAME resource body. All identity families
are computed from this tree. Slot indices preserve entire original contracts;
no Source/Auth or successful future check is stored in these instructions. -/
namespace Ash.OneShot.CoreCallableFiniteResourceTemplate
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract sequenceRows)
open CoreCallableContractAdmission CoreCallableReceiverRefinement
open CoreCallableStaticProducer (Bindings BindingRef StaticTree)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies)
open RecursiveRequirements (Requirements)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableFiniteCellRegistry (CellApi)
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

theorem name_instantiates (valid : nameCheck binder world name = true) :
    name.instantiate (Instantiation.Environment.empty.bind binder identity) = .activation (nameValue identity name) := by
  cases name with
  | activation value => rfl
  | bound name =>
    have same : name = binder := of_decide_eq_true valid
    subst name
    simp [Instantiation.ResourceName.instantiate,Instantiation.Environment.bind,nameValue]

theorem name_issued (valid : nameCheck binder world name = true) : nameValue identity name ∈ world ++ [identity] := by
  cases name with
  | activation value => exact List.mem_append_left _ (of_decide_eq_true valid)
  | bound name => exact List.mem_append_right _ (by simp [nameValue])

theorem ContractPattern.constant {pattern : ContractPattern} (closed : pattern.closed = true) :
    pattern.value original identity = pattern.value original other := by
  induction pattern with
  | reference name => cases name <;> simp_all [ContractPattern.closed,ContractPattern.value,nameValue]
  | pair left right ihL ihR =>
    obtain ⟨a,b⟩ : left.closed = true ∧ right.closed = true := by simpa [ContractPattern.closed] using closed
    simp only [ContractPattern.value,ihL a,ihR b]
  | unit | boolean | integer | slot => rfl

theorem slot_exact (located : original[index]? = some (name,contract)) :
    (ContractPattern.slot index).value original identity = contract := by simp [ContractPattern.value,slotContract,located]

theorem bindings_constant (closed : contextClosed context = true) :
    bindings original identity context = bindings original other context := by
  induction context with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨a,b⟩ : entry.2.closed = true ∧ contextClosed rest = true := by simpa [contextClosed] using closed
    simp only [bindings,ih b]
    rw [ContractPattern.constant (original := original) (identity := identity) (other := other) a]

 theorem aligned_realization (whole remaining : Bindings) (context : Context) (index identity : Nat)
    (valid : aligned remaining context index = true)
    (slots : ∀ offset, slotContract whole (index+offset) = slotContract remaining offset) :
    bindings whole identity context = remaining := by
  induction remaining generalizing index context with
  | nil =>
      cases context with
      | nil => rfl
      | cons => simp [aligned] at valid
  | cons entry rest ih =>
      cases context with
      | nil => simp [aligned] at valid
      | cons selected tail =>
          obtain ⟨⟨name,pattern⟩,next⟩ :
              (decide (selected.1 = entry.1) = true ∧ decide (selected.2 = .slot index) = true) ∧
              aligned rest tail (index+1) = true := by simpa [aligned] using valid
          have headSlot : slotContract whole index = entry.2 := by
            simpa [slotContract] using slots 0
          have tailSlots : ∀ offset, slotContract whole (index+1+offset) = slotContract rest offset := by
            intro offset
            simpa [slotContract,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using slots (offset+1)
          simp only [bindings,of_decide_eq_true name,of_decide_eq_true pattern,ContractPattern.value,headSlot,
            ih tail (index+1) next tailSlots]

 theorem aligned_original (valid : aligned original context = true) : bindings original identity context = original :=
  aligned_realization original original context 0 identity valid (fun _ => by simp)

 theorem contextTemplate_aligned (original : Bindings) (index : Nat) : aligned original (contextTemplate original index) index = true := by
  induction original generalizing index with
  | nil => rfl
  | cons entry rest ih => simp [aligned,contextTemplate,ih]

 theorem contextTemplate_closed (original : Bindings) (index : Nat) : contextClosed (contextTemplate original index) = true := by
  induction original generalizing index with
  | nil => rfl
  | cons entry rest ih => simpa [contextTemplate,contextClosed,ContractPattern.closed] using ih (index+1)

theorem LocalRef.realize_check (original : Bindings) (identity : Nat) (reference : LocalRef context name pattern) : (reference.realize (original := original) (identity := identity)).check = reference.check := by
  induction reference with
  | head => rfl
  | tail next ih => simp [LocalRef.realize,BindingRef.check,LocalRef.check,ih]

 theorem ContractPattern.formed {pattern : ContractPattern}
    (valid : pattern.check original binder world = true) :
    ScopedPorts.InWorld (world ++ [identity]) (pattern.value original identity).port := by
  induction pattern with
  | unit | boolean | integer =>
      simp [ContractPattern.value,ScopedPorts.InWorld,Contract.port,Contract.value,
        SourcePlannedTyping.Value.erase,SourceDependencyAnnotations.Value.erase,
        CoherentSourceTypes.Value.port,ScopedPorts.Port.resources]
  | reference name =>
      have issued := name_issued (identity := identity) valid
      simpa [ContractPattern.value,ScopedPorts.InWorld,Contract.port,Contract.value,
        SourcePlannedTyping.Value.erase,SourceDependencyAnnotations.Value.erase,
        CoherentSourceTypes.Value.port,ScopedPorts.Port.resources] using issued
  | pair left right ihL ihR =>
      obtain ⟨a,b⟩ : left.check original binder world = true ∧ right.check original binder world = true :=
        by simpa [ContractPattern.check] using valid
      simpa [ContractPattern.value,ScopedPorts.InWorld,Contract.port,Contract.value,
        SourcePlannedTyping.Value.erase,SourceDependencyAnnotations.Value.erase,
        CoherentSourceTypes.Value.port,ScopedPorts.Port.resources] using List.append_subset.mpr ⟨ihL a,ihR b⟩
  | slot index =>
      obtain ⟨_,ports⟩ : decide (index < original.length) = true ∧
          CoreCallableGraphAnnotationChecks.subsetB (slotContract original index).port.resources world = true :=
        by simpa [ContractPattern.check] using valid
      exact (CoreCallableGraphAnnotationChecks.subsetB_sound ports).trans (List.subset_append_left _ _)

theorem allowedName_sound (valid : allowedName binder residual name = true) :
    .cell (nameValue identity name) ∈ Instance.cell identity :: residual := by
  cases name with
  | bound name => simp [nameValue]
  | activation value => exact List.mem_cons_of_mem _ (of_decide_eq_true valid)

/-- Output-only provenance; the input contains only finite tree data. -/
structure Derived (api : CellApi) (entries : CoreCallableStaticProducer.OperationEntries)
    (policy : Syntax.TicketPolicy) (outward : List Instance) (owners : CoreCallableContractRegistries.Owners)
    (world : List Nat) (residual : List Instance) (scope : Execution.Scope)
    (original : Bindings) (binder identity : Nat) (body : Body context code pattern) where
  source : IndexedSource (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward owners
    (world ++ [identity]) (.cell identity :: residual) scope
    (CoreCallableStaticProducer.environment (bindings original identity context))
    (code.instantiate (Instantiation.Environment.empty.bind binder identity))
    (pattern.value original identity) [] (body.requirements identity) (body.plan identity) (body.rows identity)
  tree : StaticTree _ outward source

 theorem Body.derive (body : Body context code pattern)
    (apiValid : api.check = true) (valid : body.check original binder world residual = true) :
    Derived api entries policy outward owners world residual scope original binder identity body := by
  induction body with
  | unit => exact ⟨.unit,.unit⟩
  | boolean value => exact ⟨.boolean,.boolean⟩
  | integer value => exact ⟨.integer,.integer⟩
  | reference name =>
      have issued := name_issued (identity := identity) valid
      have realized := name_instantiates (identity := identity) valid
      exact ⟨by simpa [Code.instantiate,realized,ContractPattern.value,Body.dependencies,Body.requirements,Body.plan,Body.rows]
        using (IndexedSource.reference (registry := CoreCallableFiniteCellRegistry.registry (some api) entries policy)
          (outward := outward) (owners := owners) (allowed := .cell identity :: residual)
          (scope := scope) (environment := CoreCallableStaticProducer.environment (bindings original identity _)) issued),
        by simp only [Code.instantiate,realized]; exact .reference (issued := issued)⟩
  | «variable» ref =>
      obtain ⟨located,formed⟩ : ref.check = true ∧ _ := by simpa [Body.check] using valid
      have known := (ref.realize (original := original) (identity := identity)).sound
        (by simpa only [LocalRef.realize_check] using located)
      exact ⟨.variable known (ContractPattern.formed formed),.variable (known := known) (formed := ContractPattern.formed formed)⟩
  | pair left right ihL ihR =>
      obtain ⟨a,b⟩ : left.check original binder world residual = true ∧ right.check original binder world residual = true :=
        by simpa [Body.check] using valid
      let l := ihL a
      let r := ihR b
      exact ⟨by simpa [Code.instantiate,ContractPattern.value,Body.dependencies,Body.requirements,Body.plan,Body.rows] using
        (IndexedSource.pair l.source r.source),by simpa [Code.instantiate,ContractPattern.value,Body.dependencies,Body.requirements,Body.plan,Body.rows] using StaticTree.pair l.tree r.tree⟩
  | bind left right ihL ihR =>
      obtain ⟨a,b⟩ : left.check original binder world residual = true ∧ right.check original binder world residual = true :=
        by simpa [Body.check] using valid
      let l := ihL a
      let r := ihR b
      exact ⟨by simpa [Code.instantiate,bindings,CoreCallableStaticProducer.environment,Body.dependencies,Body.requirements,Body.plan,Body.rows] using
        (IndexedSource.bind l.source r.source),by simpa [Code.instantiate,bindings,CoreCallableStaticProducer.environment,Body.dependencies,Body.requirements,Body.plan,Body.rows] using StaticTree.bind l.tree r.tree⟩
  | read operand ih =>
      obtain ⟨⟨a,n⟩,allowed⟩ : (operand.check original binder world residual = true ∧
          nameCheck binder world _ = true) ∧ allowedName binder residual _ = true :=
        by simpa [Body.check,Bool.and_eq_true] using valid
      let o := ih a
      have realized := name_instantiates (identity := identity) n
      exact ⟨by simpa [Code.instantiate,Instantiation.Effect.instantiate,realized,Instantiation.freezeEffect,
        ContractPattern.value,Body.dependencies,Body.requirements,Body.plan,Body.rows] using
        (IndexedSource.perform (CoreCallableFiniteCellRegistry.read_known apiValid)
          (allowedName_sound allowed) o.source (List.nil_subset _)),
        by simpa [Code.instantiate,Instantiation.Effect.instantiate,realized,Instantiation.freezeEffect,ContractPattern.value,Body.dependencies,Body.requirements,Body.plan,Body.rows] using StaticTree.perform (known := CoreCallableFiniteCellRegistry.read_known apiValid) (admitted := allowedName_sound allowed) (formed := List.nil_subset _) o.tree⟩
  | write operand ih =>
      obtain ⟨⟨a,n⟩,allowed⟩ : (operand.check original binder world residual = true ∧
          nameCheck binder world _ = true) ∧ allowedName binder residual _ = true :=
        by simpa [Body.check,Bool.and_eq_true] using valid
      let o := ih a
      have realized := name_instantiates (identity := identity) n
      exact ⟨by simpa [Code.instantiate,Instantiation.Effect.instantiate,realized,Instantiation.freezeEffect,
        ContractPattern.value,Body.dependencies,Body.requirements,Body.plan,Body.rows] using
        (IndexedSource.perform (CoreCallableFiniteCellRegistry.write_known apiValid)
          (allowedName_sound allowed) o.source (List.nil_subset _)),
        by simpa [Code.instantiate,Instantiation.Effect.instantiate,realized,Instantiation.freezeEffect,ContractPattern.value,Body.dependencies,Body.requirements,Body.plan,Body.rows] using StaticTree.perform (known := CoreCallableFiniteCellRegistry.write_known apiValid) (admitted := allowedName_sound allowed) (formed := List.nil_subset _) o.tree⟩

 theorem ContractPattern.formed_closed {pattern : ContractPattern}
    (valid : pattern.check original binder world = true) (closed : pattern.closed = true) :
    ScopedPorts.InWorld world (pattern.value original identity).port := by
  induction pattern with
  | unit | boolean | integer =>
      simp [ContractPattern.value,ScopedPorts.InWorld,Contract.port,Contract.value,
        SourcePlannedTyping.Value.erase,SourceDependencyAnnotations.Value.erase,
        CoherentSourceTypes.Value.port,ScopedPorts.Port.resources]
  | reference name =>
      cases name with
      | bound name => simp [ContractPattern.closed] at closed
      | activation value =>
        have issued : value ∈ world := of_decide_eq_true valid
        simpa [ContractPattern.value,nameValue,ScopedPorts.InWorld,Contract.port,Contract.value,
          SourcePlannedTyping.Value.erase,SourceDependencyAnnotations.Value.erase,
          CoherentSourceTypes.Value.port,ScopedPorts.Port.resources] using issued
  | pair left right ihL ihR =>
      obtain ⟨a,b⟩ : left.check original binder world = true ∧ right.check original binder world = true :=
        by simpa [ContractPattern.check] using valid
      obtain ⟨c,d⟩ : left.closed = true ∧ right.closed = true := by simpa [ContractPattern.closed] using closed
      simpa [ContractPattern.value,ScopedPorts.InWorld,Contract.port,Contract.value,
        SourcePlannedTyping.Value.erase,SourceDependencyAnnotations.Value.erase,
        CoherentSourceTypes.Value.port,ScopedPorts.Port.resources] using List.append_subset.mpr ⟨ihL a c,ihR b d⟩
  | slot index =>
      obtain ⟨_,ports⟩ : decide (index < original.length) = true ∧
          CoreCallableGraphAnnotationChecks.subsetB (slotContract original index).port.resources world = true :=
        by simpa [ContractPattern.check] using valid
      exact CoreCallableGraphAnnotationChecks.subsetB_sound ports

 theorem outsideName_exact (valid : nameCheck binder world name = true) (fresh : identity ∉ world) :
    CallableProtection.outsideCell identity [⟨.cell (nameValue identity name),operation,false⟩] = outsideName operation name := by
  cases name with
  | bound name => simp [CallableProtection.outsideCell,nameValue,outsideName]
  | activation value =>
      have different : value ≠ identity := by intro same; subst value; exact fresh (of_decide_eq_true valid)
      simp [CallableProtection.outsideCell,nameValue,outsideName,different]

 theorem Body.hides (body : Body context code pattern)
    (valid : body.check original binder world residual = true) (fresh : identity ∉ world) :
    ResourceRequirements.Hides identity (body.requirements identity) body.outsideRequirements := by
  induction body with
  | unit | boolean | integer | reference | «variable» => exact .request
  | pair left right ihL ihR | bind left right ihL ihR =>
      obtain ⟨a,b⟩ : left.check original binder world residual = true ∧ right.check original binder world residual = true :=
        by simpa [Body.check] using valid
      exact .sequence (ihL a) (ihR b)
  | @read context code name operand ih =>
      obtain ⟨⟨a,n⟩,_⟩ : (operand.check original binder world residual = true ∧ nameCheck binder world name = true) ∧ _ :=
        by simpa [Body.check] using valid
      simpa only [Body.requirements,Body.outsideRequirements, outsideName_exact n fresh] using
        (ResourceRequirements.Hides.emitAfter (raw := [⟨.cell (nameValue identity name),0,false⟩]) (ih a))
  | @write context code name operand ih =>
      obtain ⟨⟨a,n⟩,_⟩ : (operand.check original binder world residual = true ∧ nameCheck binder world name = true) ∧ _ :=
        by simpa [Body.check] using valid
      simpa only [Body.requirements,Body.outsideRequirements, outsideName_exact n fresh] using
        (ResourceRequirements.Hides.emitAfter (raw := [⟨.cell (nameValue identity name),1,false⟩]) (ih a))

 theorem opening_known {code : Code} {binder identity : Nat} (known : LexicalBounds.Known lexical code.dependencies) :
    LexicalBounds.Known lexical
      (code.instantiate (Instantiation.Environment.empty.bind binder identity)).dependencies := by
  intro name member
  have included := acquisition_dependency_bound binder identity code member
  rcases List.mem_append.mp included with original | extra
  · exact known name original
  · simp at extra

 theorem opening_bounds {code : Code} {binder identity : Nat} {lexical : LexicalBounds}
    (bounds : SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Bounds lexical.environment code.dependencies receiver) :
    SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Bounds lexical.environment
      (code.instantiate (Instantiation.Environment.empty.bind binder identity)).dependencies (identity :: receiver) := by
  apply SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mpr
  intro value member
  obtain ⟨dependency,present,retained⟩ := List.mem_flatMap.mp member
  have included := acquisition_dependency_bound binder identity code present
  rcases List.mem_append.mp included with original | extra
  · exact List.mem_cons_of_mem _ (SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mp bounds
      (List.mem_flatMap.mpr ⟨dependency,original,retained⟩))
  · have same : dependency = Syntax.Dependency.resource identity := by simpa using extra
    subst dependency
    exact List.mem_cons.mpr (Or.inl (by simpa [ScopedPorts.Support.evaluate] using retained))

/-- The finite validator checks the literal body and original support exactly
once. Its successful output derives all fresh openings structurally. -/
def openingCheck (body : Body context code pattern) (api : CellApi) (original : Bindings)
    (binder : Nat) (world : List Nat) (residual : List Instance) (lexical : LexicalBounds) (receiver : List Nat) : Bool :=
  api.check && body.check original binder world residual && contextClosed context && aligned original context && pattern.closed &&
  pattern.check original binder world && CoreCallableGraphAnnotationChecks.knownB lexical code.dependencies &&
  CoreCallableGraphAnnotationChecks.subsetB (ScopedPorts.Support.evaluate lexical.environment code.dependencies) receiver &&
  CoreCallableGraphAnnotationChecks.subsetB receiver world

structure Opening (api : CellApi) (entries : CoreCallableStaticProducer.OperationEntries)
    (policy : Syntax.TicketPolicy) (outward : List Instance) (owners : CoreCallableContractRegistries.Owners)
    (world : List Nat) (residual : List Instance) (scope : Execution.Scope)
    (original : Bindings) (binder : Nat) (body : Body context code pattern)
    (lexical : LexicalBounds) (receiver : List Nat) where
  source : ∀ identity, identity ∉ world → IndexedSource
    (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward owners
    (world ++ [identity]) (.cell identity :: residual) scope
    (CoreCallableStaticProducer.environment original)
    (code.instantiate (Instantiation.Environment.empty.bind binder identity))
    (pattern.value original 0) [] (body.requirements identity) (body.plan identity) (body.rows identity)
  auth : ∀ identity (fresh : identity ∉ world), Authenticated
    (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward (source identity fresh) lexical (identity :: receiver)
  formed : ScopedPorts.InWorld world (pattern.value original 0).port
  hidden : ∀ identity, identity ∉ world → ResourceRequirements.Hides identity
    (body.requirements identity) body.outsideRequirements
  receiverIssued : receiver ⊆ world

 theorem check_opening (body : Body context code pattern)
    (accepted : openingCheck body api original binder world residual lexical receiver = true) :
    Opening api entries policy outward owners world residual scope original binder body lexical receiver := by
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨a,b⟩,c⟩,h⟩,d⟩,e⟩,f⟩,g⟩,r⟩ := (by simpa only [openingCheck,Bool.and_eq_true] using accepted)
  have apiValid : api.check = true := a
  have bodyValid : body.check original binder world residual = true := b
  have outClosed : pattern.closed = true := d
  have outValid : pattern.check original binder world = true := e
  have known := CoreCallableGraphAnnotationChecks.knownB_sound f
  have bounds := SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mpr (CoreCallableGraphAnnotationChecks.subsetB_sound g)
  have env : ∀ identity, bindings original identity context = original := fun _ => aligned_original h
  have output : ∀ identity, pattern.value original identity = pattern.value original 0 := fun _ => ContractPattern.constant outClosed
  let derived := fun identity => body.derive (entries := entries) (policy := policy) (outward := outward) (owners := owners)
    (scope := scope) (identity := identity) apiValid bodyValid
  let src := fun identity => ((derived identity).source.world_weaken (List.Subset.refl _))
  refine ⟨fun identity _ => by simpa only [env identity,output identity] using src identity,?_,
    ContractPattern.formed_closed outValid outClosed,fun _ fresh => body.hides bodyValid fresh,CoreCallableGraphAnnotationChecks.subsetB_sound r⟩
  intro identity fresh
  simpa only [src,env identity,output identity] using
    (derived identity).tree.authenticate_world (List.Subset.refl _) (opening_known known) (opening_bounds bounds)

/-- Resource check remains a separate additive entry point; it does not claim
the existing StaticProducer grammar has gained its resource branch. -/
def resourceCheck (body : Body context code pattern) (api : CellApi) (original : Bindings)
    (binder : Nat) (world : List Nat) (residual allowed : List Instance) (lexical : LexicalBounds) (receiver : List Nat) : Bool :=
  openingCheck body api original binder world residual lexical receiver &&
  CoreCallableGraphAnnotationChecks.subsetB (residual.flatMap Instance.resources) world &&
  CoreCallableGraphAnnotationChecks.subsetB residual allowed

structure ResourceResult (api : CellApi) (entries : CoreCallableStaticProducer.OperationEntries)
    (policy : Syntax.TicketPolicy) (outward : List Instance) (owners : CoreCallableContractRegistries.Owners)
    (world : List Nat) (allowed : List Instance) (scope : Execution.Scope)
    (original : Bindings) (binder : Nat) (payload : Int) (body : Body context code pattern)
    (lexical : LexicalBounds) (receiver : List Nat) where
  source : IndexedSource (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward owners
    world allowed scope (CoreCallableStaticProducer.environment original)
    (.resource binder (.integer payload) code) (pattern.value original 0) []
    (.sequence (.request [] []) body.outsideRequirements) body.resourcePlan body.resourceRows
  auth : Authenticated (CoreCallableFiniteCellRegistry.registry (some api) entries policy) outward source lexical receiver

 theorem check_resource (body : Body context code pattern) (payload : Int)
    (accepted : resourceCheck body api original binder world residual allowed lexical receiver = true) :
    ResourceResult api entries policy outward owners world allowed scope original binder payload body lexical receiver := by
  obtain ⟨⟨o,e⟩,a⟩ : (openingCheck body api original binder world residual lexical receiver = true ∧
      CoreCallableGraphAnnotationChecks.subsetB (residual.flatMap Instance.resources) world = true) ∧
      CoreCallableGraphAnnotationChecks.subsetB residual allowed = true := by simpa [resourceCheck] using accepted
  let opened := check_opening (entries := entries) (policy := policy) (outward := outward) (owners := owners)
    (scope := scope) body o
  have effects := CoreCallableGraphAnnotationChecks.subsetB_sound e
  have admitted := CoreCallableGraphAnnotationChecks.subsetB_sound a
  have rawBounds : SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Bounds
      lexical.environment code.dependencies receiver := by
    apply SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mpr
    have guards := o
    simp only [openingCheck,Bool.and_eq_true] at guards
    exact CoreCallableGraphAnnotationChecks.subsetB_sound guards.1.2
  let initial := IndexedSource.integer (registry := CoreCallableFiniteCellRegistry.registry (some api) entries policy)
    (outward := outward) (owners := owners) (world := world) (allowed := allowed) (scope := scope)
    (environment := CoreCallableStaticProducer.environment original) (value := payload)
  let source := IndexedSource.resource (binder := binder) initial opened.source opened.formed effects admitted opened.hidden
  refine ⟨source, .checked ?_ (.resource (bodySource := opened.source) (formed := opened.formed)
    (effectsBound := effects) (admitted := admitted) (hidden := opened.hidden)
    (.checked (by constructor) .integer) opened.auth)⟩
  simpa only [Code.dependencies,List.nil_append] using rawBounds

#print axioms name_instantiates
#print axioms name_issued
#print axioms ContractPattern.constant
#print axioms slot_exact
#print axioms bindings_constant
#print axioms aligned_realization
#print axioms aligned_original
#print axioms contextTemplate_aligned
#print axioms contextTemplate_closed
#print axioms LocalRef.realize_check
#print axioms ContractPattern.formed
#print axioms allowedName_sound
#print axioms Body.derive
#print axioms ContractPattern.formed_closed
#print axioms outsideName_exact
#print axioms Body.hides
#print axioms opening_known
#print axioms opening_bounds
#print axioms check_opening
#print axioms check_resource

end Ash.OneShot.CoreCallableFiniteResourceTemplate
