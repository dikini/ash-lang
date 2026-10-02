import CoreCallableStorageRecipes
import CoreCallableCapturedRecipes
import CoreCallableFiniteCellRegistry
import CoreCallableCompositionalResourceOpening
namespace Ash.OneShot.CoreCallableCompositionalResourceStorage
open ScopedExpressions ScopedExecution
open CallableContracts (Contract Derives Captures CaptureAtom)
open CoreCallableReceiverRefinement (LexicalBounds)

/-- Fresh is symbolic; original opaque identities remain literal data. -/
inductive Atom where
  | old : Nat → Atom
  | fresh
  deriving DecidableEq, Repr

def Atom.value (identity : Nat) : Atom → Nat
  | .old name => name
  | .fresh => identity

def Atom.valid (world : List Nat) : Atom → Bool
  | .old name => decide (name ∈ world)
  | .fresh => true

inductive Tree where
  | storage : List Atom → Tree
  | pair : Tree → Tree → Tree
  | function : List Atom → Tree → Tree → Tree
  deriving DecidableEq, Repr

def Tree.value (identity : Nat) : Tree → Contract
  | .storage atoms => .storage (atoms.map (Atom.value identity))
  | .pair first second => .pair (first.value identity) (second.value identity)
  | .function captures input output => .function (captures.map (Atom.value identity)) (input.value identity) (output.value identity)

def Tree.storageOf : Tree → List Atom
  | .storage atoms => atoms
  | .pair first second => first.storageOf ++ second.storageOf
  | .function captures _ _ => captures

def Tree.valid (world : List Nat) : Tree → Bool
  | .storage atoms => atoms.all (Atom.valid world)
  | .pair first second => first.valid world && second.valid world
  | .function captures input output => captures.all (Atom.valid world) && input.valid world && output.valid world

def Tree.original : Contract → Tree
  | .storage atoms => .storage (atoms.map Atom.old)
  | .pair first second => .pair (Tree.original first) (Tree.original second)
  | .function captures input output => .function (captures.map Atom.old) (Tree.original input) (Tree.original output)

abbrev Bindings := List (Nat × Tree)
def lookup : Bindings → Nat → Option Tree
  | [],_ => none
  | (key,value)::rest,name => if name = key then some value else lookup rest name

def realize (identity : Nat) (bindings : Bindings) : CoreCallableReturnStorageProducer.Bindings :=
  bindings.map fun (name,value) => (name,value.value identity)

def original (bindings : CoreCallableReturnStorageProducer.Bindings) : Bindings :=
  bindings.map fun (name,value) => (name,Tree.original value)

private theorem andTrue {a b : Bool} (valid : (a && b) = true) : a = true ∧ b = true := by
  simpa only [Bool.and_eq_true] using valid

theorem Tree.original_value (contract : Contract) : (Tree.original contract).value identity = contract := by
  induction contract <;> simp_all [Tree.original,Tree.value,List.map_map,Atom.value,Function.comp_def]

theorem Tree.storage_value (tree : Tree) : (tree.value identity).storageOf = tree.storageOf.map (Atom.value identity) := by
  induction tree <;> simp_all [Tree.value,Tree.storageOf,Contract.storageOf]

theorem lookup_realize (bindings : Bindings) (name : Nat) :
    CoreCallableReturnStorageProducer.lookup (realize identity bindings) name = (lookup bindings name).map (Tree.value identity) := by
  induction bindings with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key,value⟩
      by_cases same : name = key
      · simp [realize,lookup,CoreCallableReturnStorageProducer.lookup,same]
      · simpa [realize,lookup,CoreCallableReturnStorageProducer.lookup,same] using ih

theorem realize_original (bindings : CoreCallableReturnStorageProducer.Bindings) : realize identity (original bindings) = bindings := by
  induction bindings with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨name,value⟩
      change (name,(Tree.original value).value identity)::realize identity (original rest) = (name,value)::rest
      rw [Tree.original_value,ih]

theorem Atom.value_injective (a b : Atom) (first : a.valid world = true) (second : b.valid world = true)
    (fresh : identity ∉ world) (same : a.value identity = b.value identity) : a = b := by
  cases a with
  | fresh =>
      cases b with
      | fresh => rfl
      | old name =>
          change identity = name at same
          subst name
          exact False.elim (fresh (of_decide_eq_true second))
  | old name =>
      cases b with
      | fresh =>
          change name = identity at same
          subst name
          exact False.elim (fresh (of_decide_eq_true first))
      | old other => exact congrArg Atom.old same

theorem atoms_value_injective (first second : List Atom)
    (a : first.all (Atom.valid world) = true) (b : second.all (Atom.valid world) = true)
    (fresh : identity ∉ world) (same : first.map (Atom.value identity) = second.map (Atom.value identity)) : first = second := by
  induction first generalizing second with
  | nil => cases second <;> simp_all
  | cons head rest ih =>
      cases second with
      | nil => simp at same
      | cons other tail =>
          obtain ⟨h,t⟩ := List.cons.inj same
          obtain ⟨aH,aT⟩ : head.valid world = true ∧ rest.all (Atom.valid world) = true := by simpa using a
          obtain ⟨bH,bT⟩ : other.valid world = true ∧ tail.all (Atom.valid world) = true := by simpa using b
          rw [head.value_injective other aH bH fresh h,ih tail aT bT t]

theorem Tree.value_injective (first second : Tree) (a : first.valid world = true) (b : second.valid world = true)
    (fresh : identity ∉ world) (same : first.value identity = second.value identity) : first = second := by
  induction first generalizing second with
  | storage atoms =>
      cases second with
      | storage other => exact congrArg Tree.storage (atoms_value_injective atoms other a b fresh (Contract.storage.inj same))
      | pair | function => cases same
  | pair left right ihL ihR =>
      cases second with
      | storage | function => cases same
      | pair l r =>
          obtain ⟨aL,aR⟩ := andTrue a
          obtain ⟨bL,bR⟩ := andTrue b
          obtain ⟨sameL,sameR⟩ := Contract.pair.inj same
          rw [ihL l aL bL sameL,ihR r aR bR sameR]
  | function captures input output ihI ihO =>
      cases second with
      | storage | pair => cases same
      | function cap i o =>
          obtain ⟨⟨aC,aI⟩,aO⟩ : (captures.all (Atom.valid world) = true ∧ input.valid world = true) ∧ output.valid world = true := by simpa [Tree.valid,Bool.and_eq_true] using a
          obtain ⟨⟨bC,bI⟩,bO⟩ : (cap.all (Atom.valid world) = true ∧ i.valid world = true) ∧ o.valid world = true := by simpa [Tree.valid,Bool.and_eq_true] using b
          obtain ⟨sameC,sameI,sameO⟩ := Contract.function.inj same
          rw [atoms_value_injective captures cap aC bC fresh sameC,ihI i aI bI sameI,ihO o aO bO sameO]

/-- Literal recipes select exact whole current trees, never erased rich ports. -/
def template (bindings : Bindings) (binder : Nat) : CoreCallableStorageRecipes.ContractTemplate → Option Tree
  | .slot name => lookup bindings name
  | .storage atoms => (bounds bindings binder atoms).map Tree.storage
  | .pair first second => do return .pair (← template bindings binder first) (← template bindings binder second)
  | .function atoms input output => do return .function (← bounds bindings binder atoms) (← template bindings binder input) (← template bindings binder output)
where
  bounds (bindings : Bindings) (binder : Nat) : List CoreCallableStorageRecipes.BoundAtom → Option (List Atom)
    | [] => some []
    | head::tail => do
        let value ← match head with
          | .activation name => some [Atom.old name]
          | .resourceBinder name => if name = binder then some [Atom.fresh] else none
          | .slot name => (lookup bindings name).map Tree.storageOf
        return value ++ (← bounds bindings binder tail)

def collect (bindings : Bindings) : List Syntax.Dependency → Option (List Atom)
  | [] => some []
  | .resource name::rest => (collect bindings rest).map (Atom.old name :: ·)
  | .variable name::rest => do
      let value ← lookup bindings name
      return value.storageOf ++ (← collect bindings rest)
  | .ticket _::_ => none

def captures (bindings : Bindings) (binder : Nat) (code : Code) : Option (List Atom) := do
  let atoms ← collect bindings code.dependencies
  return atoms ++ (if binder ∈ code.freeNames then [.fresh] else [])

private theorem captures_mono (captured : Captures environment first deps) (larger : first ⊆ second) :
    Captures environment second deps := by
  apply CallableContracts.captures_iff.mpr
  intro dependency member
  cases CallableContracts.captures_iff.mp captured dependency member with
  | resource included => exact .resource (larger included)
  | «variable» known included => exact .variable known (included.trans larger)

theorem collect_sound (accepted : collect bindings deps = some atoms) :
    Captures (CoreCallableReturnStorageProducer.environment (realize identity bindings))
      (atoms.map (Atom.value identity)) deps := by
  induction deps generalizing atoms with
  | nil => cases Option.some.inj accepted; exact .nil
  | cons head rest ih =>
      cases head with
      | ticket name => simp [collect] at accepted
      | resource name =>
          cases checked : collect bindings rest with
          | none => simp [collect,checked] at accepted
          | some tail =>
              have equal : Atom.old name::tail = atoms := by simpa [collect,checked] using accepted
              subst atoms
              exact .cons (.resource (by simp [Atom.value]))
                (captures_mono (ih checked) (List.subset_cons_of_subset _ (List.Subset.refl _)))
      | «variable» name =>
          cases found : lookup bindings name with
          | none => simp [collect,found] at accepted
          | some value =>
              cases checked : collect bindings rest with
              | none => simp [collect,found,checked] at accepted
              | some tail =>
                  have equal : value.storageOf ++ tail = atoms := by simpa [collect,found,checked] using accepted
                  subst atoms
                  have known : CoreCallableReturnStorageProducer.environment (realize identity bindings) name = some (value.value identity) := by
                    simp [CoreCallableReturnStorageProducer.environment,lookup_realize,found]
                  apply Captures.cons (.variable known (by rw [Tree.storage_value,List.map_append]; exact List.subset_append_left _ _))
                  exact captures_mono (ih checked) (by rw [List.map_append]; exact List.subset_append_right _ _)

theorem captures_opened (accepted : captures bindings binder code = some atoms) :
    Captures (CoreCallableReturnStorageProducer.environment (realize identity bindings)) (atoms.map (Atom.value identity))
      (code.instantiate (Instantiation.Environment.empty.bind binder identity)).dependencies := by
  cases checked : collect bindings code.dependencies with
  | none => simp [captures,checked] at accepted
  | some originalAtoms =>
      by_cases present : binder ∈ code.freeNames
      · have equal : originalAtoms ++ [.fresh] = atoms := by simpa [captures,checked,present] using accepted
        subst atoms
        have original := collect_sound (identity := identity) checked
        apply CallableContracts.captures_iff.mpr
        intro dep member
        rcases List.mem_append.mp (acquisition_dependency_bound binder identity code member) with old | introduced
        · cases CallableContracts.captures_iff.mp original dep old with
          | resource included => exact .resource (by simp only [List.map_append]; exact List.mem_append_left _ included)
          | «variable» known included => exact .variable known (included.trans (by simp only [List.map_append]; exact List.subset_append_left _ _))
        · have same : dep = .resource identity := by simpa using introduced
          subst dep
          exact .resource (by simp [Atom.value])
      · have equal : originalAtoms = atoms := by simpa [captures,checked,present] using accepted
        subst atoms
        have missing : Missing (Instantiation.Environment.empty.bind binder identity) code.freeNames := by
          intro name member
          have different : name ≠ binder := fun same => present (same ▸ member)
          simp [Instantiation.Environment.bind,Instantiation.Environment.empty,different]
        rw [code.instantiation_identity _ missing]
        exact collect_sound checked

def nameAtom (binder : Nat) : Instantiation.ResourceName → Option Atom
  | .activation name => some (.old name)
  | .bound name => if name = binder then some .fresh else none

theorem nameAtom_sound (accepted : nameAtom binder name = some atom) :
    name.instantiate (Instantiation.Environment.empty.bind binder identity) = .activation (atom.value identity) := by
  cases name with
  | activation name => cases Option.some.inj accepted; rfl
  | bound name =>
      by_cases same : name = binder
      · simp [nameAtom,same] at accepted
        subst atom
        simp [Instantiation.ResourceName.instantiate,Instantiation.Environment.bind,same,Atom.value]
      · simp [nameAtom,same] at accepted

/-- This tree is checker output. Its proof fields are current computations,
not caller storage/capture derivations in the literal recipe. -/
inductive Produced (api : CoreCallableFiniteCellRegistry.CellApi) (binder : Nat) (world : List Nat) :
    Bindings → Code → Tree → Type where
  | unit : Produced api binder world bindings .unit (.storage [])
  | boolean : Produced api binder world bindings (.boolean flag) (.storage [])
  | integer : Produced api binder world bindings (.integer value) (.storage [])
  | reference (resolved : nameAtom binder name = some atom) (issued : atom.valid world = true) :
      Produced api binder world bindings (.resourceRef name) (.storage [atom])
  | «variable» (found : lookup bindings name = some value) (valid : value.valid world = true) :
      Produced api binder world bindings (.variable name) value
  | pair (first : Produced api binder world bindings a input) (second : Produced api binder world bindings b output) :
      Produced api binder world bindings (.pair a b) (.pair input output)
  | bind (first : Produced api binder world bindings a input)
      (second : Produced api binder world ((parameter,input)::bindings) b output) :
      Produced api binder world bindings (.bind parameter a b) output
  | lambda (validInput : input.valid world = true)
      (body : Produced api binder world ((parameter,input)::bindings) code output)
      (captured : captures bindings binder (.lambda parameter code) = some bound)
      (validBound : bound.all (Atom.valid world) = true) :
      Produced api binder world bindings (.lambda parameter code) (.function bound input output)
  | app (function : Produced api binder world bindings f (.function bound input output))
      (argument : Produced api binder world bindings a input) :
      Produced api binder world bindings (.app f a) output
  | branch (condition : Produced api binder world bindings test conditionResult)
      (yes : Produced api binder world bindings a output) (no : Produced api binder world bindings b output) :
      Produced api binder world bindings (.branch test a b) output
  | read (checkedApi : api.check = true) (resolved : nameAtom binder name = some atom)
      (issued : atom.valid world = true) (operand : Produced api binder world bindings code operandResult) :
      Produced api binder world bindings (.perform (.cell name) 0 code) (.storage [])
  | write (checkedApi : api.check = true) (resolved : nameAtom binder name = some atom)
      (issued : atom.valid world = true) (operand : Produced api binder world bindings code operandResult) :
      Produced api binder world bindings (.perform (.cell name) 1 code) (.storage [])

theorem Produced.valid (produced : Produced api binder world bindings code result) : result.valid world = true := by
  induction produced with
  | unit | boolean | integer | read | write => rfl
  | reference resolved issued => simpa [Tree.valid] using issued
  | «variable» found valid => exact valid
  | pair first second ihF ihS => simp [Tree.valid,ihF,ihS]
  | bind first second ihF ihS => exact ihS
  | lambda input body captured bound ih => simp [Tree.valid,input,bound,ih]
  | app function argument ihF ihA =>
      exact (andTrue ihF).2
  | branch condition yes no ihC ihY ihN => exact ihY

@[simp] theorem realize_cons : realize identity ((name,input)::bindings) =
    CoreCallableReturnStorageProducer.extend (realize identity bindings) name (input.value identity) := rfl

theorem Produced.derive (produced : Produced api binder world bindings code result) :
    Derives declarations (CoreCallableReturnStorageProducer.environment (realize identity bindings))
      (world ++ [identity]) ticket (code.instantiate (Instantiation.Environment.empty.bind binder identity)) (result.value identity) := by
  induction produced generalizing ticket with
  | unit => exact .leaf trivial rfl .nil
  | boolean => exact .leaf trivial rfl .nil
  | integer => exact .leaf trivial rfl .nil
  | reference resolved issued =>
      rename_i name atom bindings
      have opened := nameAtom_sound (identity := identity) resolved
      simpa [Code.instantiate,opened,Tree.value] using
        (Derives.leaf (declarations := declarations) (environment := CoreCallableReturnStorageProducer.environment (realize identity bindings))
          (world := world ++ [identity]) (ticket := ticket) (bound := [Atom.value identity atom]) (code := .resourceRef (.activation (Atom.value identity atom)))
          trivial rfl (.cons (.resource (by simp)) .nil))
  | «variable» found valid =>
      exact .variable (by simp [CoreCallableReturnStorageProducer.environment,lookup_realize,found])
  | pair first second ihF ihS => exact .pair ihF ihS
  | bind first second ihF ihS =>
      simpa only [Code.instantiate,realize_cons,CoreCallableReturnStorageProducer.environment_extend] using Derives.bind ihF ihS
  | lambda validInput body captured validBound ih =>
      have checked := ih (ticket := .none)
      simpa only [Code.instantiate,Tree.value,realize_cons,CoreCallableReturnStorageProducer.environment_extend,CoreCallableReturnStorageProducer.environment,realize] using
        Derives.lambda checked (captures_opened (identity := identity) captured)
  | app function argument ihF ihA => exact .app ihF ihA
  | branch condition yes no ihC ihY ihN => exact .branch ihC ihY ihN
  | read checkedApi resolved issued operand ih =>
      rename_i name atom bindings code operandResult
      have opened := nameAtom_sound (identity := identity) resolved
      have original := CoreCallableFiniteCellRegistry.checked_original checkedApi
      cases original
      simpa [Code.instantiate,Instantiation.Effect.instantiate,opened,Tree.value,Instantiation.freezeEffect] using
        (Derives.perform (requested := .cell (Atom.value identity atom)) (operation := 0)
          (input := .reference (Atom.value identity atom)) (output := .integer) (bound := []) ih rfl rfl)
  | write checkedApi resolved issued operand ih =>
      rename_i name atom bindings code operandResult
      have opened := nameAtom_sound (identity := identity) resolved
      have original := CoreCallableFiniteCellRegistry.checked_original checkedApi
      cases original
      simpa [Code.instantiate,Instantiation.Effect.instantiate,opened,Tree.value,Instantiation.freezeEffect] using
        (Derives.perform (requested := .cell (Atom.value identity atom)) (operation := 1)
          (input := .product (.reference (Atom.value identity atom)) .integer) (output := .unit) (bound := []) ih rfl rfl)

/-- Recipes contain literal domains and child instructions only. Lambda result
and captures are computed from the original code and nearest whole slots. -/
inductive Recipe where
  | leaf | variable
  | pair : Recipe → Recipe → Recipe
  | bind : Recipe → Recipe → Recipe
  | lambda : CoreCallableStorageRecipes.ContractTemplate → Recipe → Recipe
  | app : Recipe → Recipe → Recipe
  | branch : Recipe → Recipe → Recipe → Recipe
  | cell : Recipe → Recipe
  deriving Repr

def check (api : CoreCallableFiniteCellRegistry.CellApi) (binder : Nat) (world : List Nat)
    (bindings : Bindings) : (code : Code) → Recipe → Option (Σ result, Produced api binder world bindings code result)
  | .unit,.leaf => some ⟨.storage [],.unit⟩
  | .boolean flag,.leaf => some ⟨.storage [],.boolean⟩
  | .integer value,.leaf => some ⟨.storage [],.integer⟩
  | .resourceRef name,.leaf =>
      match resolved : nameAtom binder name with
      | none => none
      | some atom => if valid : atom.valid world = true then
          some ⟨.storage [atom],.reference resolved valid⟩ else none
  | .variable name,.variable => do
      match found : lookup bindings name with
      | none => none
      | some value => if valid : value.valid world = true then
          some ⟨value,.variable found valid⟩ else none
  | .pair first second,.pair a b => do
      let ⟨input,p⟩ ← check api binder world bindings first a
      let ⟨output,q⟩ ← check api binder world bindings second b
      return ⟨.pair input output,.pair p q⟩
  | .bind parameter first second,.bind a b => do
      let ⟨input,p⟩ ← check api binder world bindings first a
      let ⟨output,q⟩ ← check api binder world ((parameter,input)::bindings) second b
      return ⟨output,.bind p q⟩
  | .lambda parameter body,.lambda domain bodyRecipe => do
      let input ← template bindings binder domain
      if validInput : input.valid world = true then
        let ⟨output,p⟩ ← check api binder world ((parameter,input)::bindings) body bodyRecipe
        match captured : captures bindings binder (.lambda parameter body) with
        | none => none
        | some bound => if validBound : bound.all (Atom.valid world) = true then
            some ⟨.function bound input output,.lambda validInput p captured validBound⟩ else none
      else none
  | .app function argument,.app f a => do
      let ⟨fn,p⟩ ← check api binder world bindings function f
      match fn,p with
      | .function bound input output,p =>
          let ⟨actual,q⟩ ← check api binder world bindings argument a
          if same : actual = input then return ⟨output,.app p (same ▸ q)⟩ else none
      | _,_ => none
  | .branch condition yes no,.branch c a b => do
      let ⟨_,p⟩ ← check api binder world bindings condition c
      let ⟨output,q⟩ ← check api binder world bindings yes a
      let ⟨other,r⟩ ← check api binder world bindings no b
      if same : other = output then return ⟨output,.branch p q (same ▸ r)⟩ else none
  | .perform (.cell name) 0 operand,.cell recipe => do
      if validApi : api.check = true then
        match resolved : nameAtom binder name with
        | none => none
        | some atom => if issued : atom.valid world = true then
            let ⟨_,p⟩ ← check api binder world bindings operand recipe
            return ⟨.storage [],.read validApi resolved issued p⟩ else none
      else none
  | .perform (.cell name) 1 operand,.cell recipe => do
      if validApi : api.check = true then
        match resolved : nameAtom binder name with
        | none => none
        | some atom => if issued : atom.valid world = true then
            let ⟨_,p⟩ ← check api binder world bindings operand recipe
            return ⟨.storage [],.write validApi resolved issued p⟩ else none
      else none
  | _,_ => none
termination_by code _ => code.nodes
decreasing_by all_goals simp only [Code.nodes]; all_goals omega

def Atom.outside (bound : List Nat) : Atom → Bool
  | .old name => decide (name ∈ bound)
  | .fresh => false

def Tree.outside (bound : List Nat) (tree : Tree) : Bool := tree.storageOf.all (Atom.outside bound)
def Tree.closed : Tree → Bool
  | .storage atoms => atoms.all (fun atom => match atom with | .old _ => true | .fresh => false)
  | .pair first second => first.closed && second.closed
  | .function captures input output =>
      captures.all (fun atom => match atom with | .old _ => true | .fresh => false) && input.closed && output.closed

theorem atoms_constant (atoms : List Atom)
    (closed : atoms.all (fun atom => match atom with | .old _ => true | .fresh => false) = true) :
    atoms.map (Atom.value first) = atoms.map (Atom.value second) := by
  apply List.map_congr_left
  intro atom member
  have valid := (List.all_eq_true.mp closed) atom member
  cases atom with
  | old name => rfl
  | fresh => contradiction

theorem Tree.constant (tree : Tree) (closed : tree.closed = true) : tree.value first = tree.value second := by
  induction tree with
  | storage atoms => exact congrArg Contract.storage (atoms_constant atoms closed)
  | pair a b ihA ihB => obtain ⟨aC,bC⟩ := andTrue closed; simp only [Tree.value,ihA aC,ihB bC]
  | function captures input output ihI ihO =>
      obtain ⟨⟨a,b⟩,c⟩ : (captures.all (fun atom => match atom with | .old _ => true | .fresh => false) = true ∧ input.closed = true) ∧ output.closed = true := by
        simpa [Tree.closed,Bool.and_eq_true] using closed
      simp only [Tree.value,atoms_constant (first := first) (second := second) captures a,ihI b,ihO c]

theorem Tree.outside_sound {tree : Tree} (accepted : tree.outside bound = true) : (tree.value identity).storageOf ⊆ bound := by
  rw [Tree.storage_value]
  intro name member
  obtain ⟨atom,located,rfl⟩ := List.mem_map.mp member
  have included := (List.all_eq_true.mp accepted) atom located
  cases atom with
  | old name => exact of_decide_eq_true included
  | fresh => contradiction

structure Opening (api : CoreCallableFiniteCellRegistry.CellApi) (binder : Nat) (world : List Nat)
    (bindings : CoreCallableReturnStorageProducer.Bindings) (code : Code) (recipe : Recipe) (bound : List Nat) where
  result : Tree
  produced : Produced api binder world (original bindings) code result
  accepted : check api binder world (original bindings) code recipe = some ⟨result,produced⟩
  outside : result.outside bound = true
  closed : result.closed = true

def opening (api : CoreCallableFiniteCellRegistry.CellApi) (binder : Nat) (world : List Nat)
    (bindings : CoreCallableReturnStorageProducer.Bindings) (code : Code) (recipe : Recipe) (bound : List Nat) :
    Option (Opening api binder world bindings code recipe bound) :=
  match accepted : check api binder world (original bindings) code recipe with
  | none => none
  | some ⟨result,produced⟩ =>
      if outside : result.outside bound = true then
        if closed : result.closed = true then some ⟨result,produced,accepted,outside,closed⟩ else none
      else none

theorem Opening.derive (receipt : Opening api binder world bindings code recipe bound) (identity : Nat) :
    Derives declarations (CoreCallableReturnStorageProducer.environment bindings) (world ++ [identity]) ticket
      (code.instantiate (Instantiation.Environment.empty.bind binder identity)) (receipt.result.value 0) ∧
    (receipt.result.value 0).storageOf ⊆ bound := by
  have derived := receipt.produced.derive (declarations := declarations) (identity := identity) (ticket := ticket)
  rw [realize_original,receipt.result.constant receipt.closed] at derived
  exact ⟨derived,receipt.result.outside_sound receipt.outside⟩

theorem bounds_specialize (accepted : template.bounds bindings binder atoms = some result) :
    CoreCallableStorageRecipes.bound (realize identity bindings) (Instantiation.Environment.empty.bind binder identity) atoms =
      some (result.map (Atom.value identity)) := by
  induction atoms generalizing result with
  | nil => cases Option.some.inj accepted; rfl
  | cons head rest ih =>
      cases head with
      | activation name =>
          cases checked : template.bounds bindings binder rest with
          | none => simp [template.bounds,checked] at accepted
          | some tail =>
              have same : Atom.old name::tail = result := by simpa [template.bounds,checked] using accepted
              subst result
              simp [CoreCallableStorageRecipes.bound,CoreCallableStorageRecipes.atom,ih checked,Atom.value]
      | resourceBinder name =>
          by_cases equal : name = binder
          · subst name
            cases checked : template.bounds bindings binder rest with
            | none => simp [template.bounds,checked] at accepted
            | some tail =>
                have same : Atom.fresh::tail = result := by simpa [template.bounds,checked] using accepted
                subst result
                simp [CoreCallableStorageRecipes.bound,CoreCallableStorageRecipes.atom,Instantiation.Environment.bind,ih checked,Atom.value]
          · simp [template.bounds,equal] at accepted
      | slot name =>
          cases found : lookup bindings name with
          | none => simp [template.bounds,found] at accepted
          | some value =>
              cases checked : template.bounds bindings binder rest with
              | none => simp [template.bounds,found,checked] at accepted
              | some tail =>
                  have same : value.storageOf ++ tail = result := by simpa [template.bounds,found,checked] using accepted
                  subst result
                  simp [CoreCallableStorageRecipes.bound,CoreCallableStorageRecipes.atom,lookup_realize,found,
                    ih checked,Tree.storage_value,List.map_append]

theorem template_specialize (recipe : CoreCallableStorageRecipes.ContractTemplate)
    (accepted : template bindings binder recipe = some result) :
    CoreCallableStorageRecipes.contract (realize identity bindings) (Instantiation.Environment.empty.bind binder identity) recipe = some (result.value identity) := by
  induction recipe generalizing result with
  | slot name =>
      change lookup bindings name = some result at accepted
      simp [CoreCallableStorageRecipes.contract,lookup_realize,accepted]
  | storage atoms =>
      cases checked : template.bounds bindings binder atoms with
      | none => simp [template,checked] at accepted
      | some bound =>
          have same : Tree.storage bound = result := by simpa [template,checked] using accepted
          subst result
          simp [CoreCallableStorageRecipes.contract,bounds_specialize checked,Tree.value]
  | pair first second ihF ihS =>
      cases a : template bindings binder first <;> cases b : template bindings binder second <;> simp [template,a,b] at accepted
      next input output =>
        subst result
        simp [CoreCallableStorageRecipes.contract,ihF a,ihS b,Tree.value]
  | function atoms input output ihI ihO =>
      cases a : template.bounds bindings binder atoms <;> cases b : template bindings binder input <;>
        cases c : template bindings binder output <;> simp [template,a,b,c] at accepted
      next bound first second =>
        subst result
        simp [CoreCallableStorageRecipes.contract,bounds_specialize a,ihI b,ihO c,Tree.value]

theorem nameAtom_free (accepted : nameAtom binder name = some atom) : name.freeNames ⊆ [binder] := by
  cases name with
  | activation name => exact List.nil_subset _
  | bound name =>
      by_cases same : name = binder
      · subst name; exact List.Subset.refl _
      · simp [nameAtom,same] at accepted

theorem Produced.free_names (produced : Produced api binder world bindings code result) : code.freeNames ⊆ [binder] := by
  induction produced with
  | unit | boolean | integer | «variable» => exact List.nil_subset _
  | reference resolved issued => exact nameAtom_free resolved
  | pair first second ihF ihS | bind first second ihF ihS | app first second ihF ihS =>
      exact List.append_subset.mpr ⟨ihF,ihS⟩
  | lambda validInput body captured validBound ih => exact ih
  | branch condition yes no ihC ihY ihN => exact List.append_subset.mpr ⟨List.append_subset.mpr ⟨ihC,ihY⟩,ihN⟩
  | read api resolved issued operand ih | write api resolved issued operand ih =>
      exact List.append_subset.mpr ⟨nameAtom_free resolved,ih⟩

theorem Opening.resource_closed (receipt : Opening api binder world bindings body recipe bound)
    (initial : CallableContracts.Derives declarations environment world ticket initializer input) :
    (Code.resource binder initializer body).ResourceClosed := by
  have closed := CallableContracts.resource_closed initial
  change initializer.freeNames = [] at closed
  have names := receipt.produced.free_names
  simp only [Code.ResourceClosed,Code.freeNames,closed,List.nil_append]
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name member
  obtain ⟨included,different⟩ := List.mem_filter.mp member
  have same : name = binder := by simpa using names included
  simp [same] at different

theorem captures_check_opened (accepted : captures bindings binder code = some atoms) :
    CoreCallableReturnStorageProducer.captureCheck (realize identity bindings) (atoms.map (Atom.value identity))
      (code.instantiate (Instantiation.Environment.empty.bind binder identity)).dependencies = true :=
  CoreCallableCapturedRecipes.captureCheck_complete (captures_opened accepted)

/-- SAME composed source indices and entire original paired maps accompany the
storage output. The original receipt is reused, never a new body derivation. -/
structure Combined
    (current : CoreCallablePairedOrigin.Origins (CoreCallableFiniteCellRegistry.registry (some api) entries policy)
      declarations outward owners world allowed scope receiver root (.resource binder initial code)
      richBindings storageBindings lexical records)
    (annotation : CoreCallableStaticProducer.Annotation entries owners richBindings initial .integer initialDemand initialReq initialPlan initialRows)
    (body : CoreCallableCompositionalResourceBody.Body richBindings context code pattern checking needs)
    (initialRecipe : CoreCallableStorageRecipes.Recipe) (bodyRecipe : Recipe)
    (residual : List Instance) (bound : List Nat) where
  source : CoreCallableCompositionalResourceOpening.Result api entries policy outward owners world residual allowed scope richBindings binder annotation body lexical receiver
  paired : CoreCallablePairedOrigin.Origins (CoreCallableFiniteCellRegistry.registry (some api) entries policy)
    declarations outward owners world allowed scope receiver root (.resource binder initial code)
    richBindings storageBindings lexical records
  pairedSame : paired = current
  initializerResult : Contract
  initializerChecked : CoreCallableStorageRecipes.check storageBindings Instantiation.Environment.empty initial initialRecipe = some initializerResult
  opening : Opening api binder world storageBindings code bodyRecipe bound
  returningIssued : bound ⊆ world
  resource : Derives declarations (CoreCallableReturnStorageProducer.environment storageBindings) world .none
    (.resource binder initial code) (opening.result.value 0)

inductive Error where
  | source : CoreCallableCompositionalResourceOpening.Error → Error
  | initializer | body | returning

def check_composed
    (current : CoreCallablePairedOrigin.Origins (CoreCallableFiniteCellRegistry.registry (some api) entries policy)
      declarations outward owners world allowed scope receiver root (.resource binder initial code)
      richBindings storageBindings lexical records)
    (annotation : CoreCallableStaticProducer.Annotation entries owners richBindings initial .integer initialDemand initialReq initialPlan initialRows)
    (body : CoreCallableCompositionalResourceBody.Body richBindings context code pattern checking needs)
    (initialRecipe : CoreCallableStorageRecipes.Recipe) (bodyRecipe : Recipe)
    (residual : List Instance) (bound : List Nat) :
    Except Error (Combined current annotation body initialRecipe bodyRecipe residual bound) := do
  let source ← (CoreCallableCompositionalResourceOpening.check_compositional annotation body api policy outward world residual allowed scope binder lexical receiver).mapError Error.source
  match initializerChecked : CoreCallableStorageRecipes.check storageBindings Instantiation.Environment.empty initial initialRecipe with
  | none => .error .initializer
  | some initializerResult =>
      match _bodyChecked : opening api binder world storageBindings code bodyRecipe bound with
      | none => .error .body
      | some opened =>
          if boundIssued : decide (bound ⊆ world) = true then
            let initialLower := CoreCallableStorageRecipes.check_sound (declarations := declarations) (world := world) (ticket := .none) initializerChecked
            let resource := Derives.resource initialLower (opened.resource_closed initialLower)
              (fun identity _ => (opened.derive (declarations := declarations) (ticket := .none) identity).1)
              ((opened.result.outside_sound opened.outside).trans (of_decide_eq_true boundIssued))
            .ok ⟨source.down,current,rfl,initializerResult,initializerChecked,opened,of_decide_eq_true boundIssued,resource⟩
          else .error .returning

/-- Reuse executed checker equalities to expose the joint result. These are
consumer hypotheses, never recipe fields or inputs to check_composed. -/
theorem check_composed_accepted
    {current : CoreCallablePairedOrigin.Origins (CoreCallableFiniteCellRegistry.registry (some api) entries policy)
      declarations outward owners world allowed scope receiver root (.resource binder initial code)
      richBindings storageBindings lexical records}
    {annotation : CoreCallableStaticProducer.Annotation entries owners richBindings initial .integer initialDemand initialReq initialPlan initialRows}
    {body : CoreCallableCompositionalResourceBody.Body richBindings context code pattern checking needs}
    {source : PLift (CoreCallableCompositionalResourceOpening.Result api entries policy outward owners world residual allowed scope richBindings binder annotation body lexical receiver)}
    (sourceAccepted : CoreCallableCompositionalResourceOpening.check_compositional annotation body api policy outward world residual allowed scope binder lexical receiver = .ok source)
    (initializerAccepted : CoreCallableStorageRecipes.check storageBindings Instantiation.Environment.empty initial initialRecipe = some initializerResult)
    (bodyAccepted : opening api binder world storageBindings code bodyRecipe bound = some opened)
    (issued : bound ⊆ world) :
    ∃ receipt, check_composed current annotation body initialRecipe bodyRecipe residual bound = .ok receipt := by
  unfold check_composed
  rw [sourceAccepted]
  simp only [Except.mapError]
  split
  · rename_i failed
    rw [failed] at initializerAccepted
    contradiction
  · rename_i actual checked
    have same := Option.some.inj (checked.symm.trans initializerAccepted)
    subst actual
    split
    · rename_i failed
      rw [failed] at bodyAccepted
      contradiction
    · rename_i actual checked
      have same := Option.some.inj (checked.symm.trans bodyAccepted)
      subst actual
      have valid : decide (bound ⊆ world) = true := decide_eq_true issued
      simp only [valid]
      exact ⟨_,rfl⟩

theorem Combined.fresh_excluded
    {current : CoreCallablePairedOrigin.Origins (CoreCallableFiniteCellRegistry.registry (some api) entries policy)
      declarations outward owners world allowed scope receiver root (.resource binder initial code)
      richBindings storageBindings lexical records}
    (receipt : Combined current annotation body initialRecipe bodyRecipe residual bound) (fresh : identity ∉ world) :
    identity ∉ (receipt.opening.result.value 0).storageOf :=
  fun retained => fresh (receipt.returningIssued (receipt.opening.result.outside_sound receipt.opening.outside retained))

#print axioms Tree.original_value
#print axioms Tree.storage_value
#print axioms lookup_realize
#print axioms realize_original
#print axioms Tree.value_injective
#print axioms collect_sound
#print axioms captures_opened
#print axioms captures_check_opened
#print axioms bounds_specialize
#print axioms template_specialize
#print axioms Produced.valid
#print axioms Produced.derive
#print axioms Produced.free_names
#print axioms Tree.constant
#print axioms Tree.outside_sound
#print axioms Opening.derive
#print axioms Opening.resource_closed
#print axioms check_composed_accepted
#print axioms Combined.fresh_excluded

end Ash.OneShot.CoreCallableCompositionalResourceStorage
