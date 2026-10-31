import NetworkLedgerCoreRegion

/-
The restricted Core fragment for the persistent tuple recognized by
`CoreInspection::persistent_tuple`. Nodes and binders are identities; a
nomination alone is not a judgment about the program. The `query` node is
the normalized default-allocation operation, so a real Core mapping must check
its effect, operation and region API identities before it can produce this node.
The recognizer below checks the query operand, captured context, request layout,
nominal constructor, and every field node in the linked graph. Evaluation
visits those field nodes left-to-right before the storage expression.

This does not yet cover function calls, pattern matching, provider confinement,
or the binding from Rust's validated arena into this model. It issues no fact.
-/
namespace Ash.NetworkLedger.CoreEval

open Ash.NetworkLedger.Allocation
open Ash.NetworkLedger.CoreRegion

abbrev NodeId := Nat
abbrev Binder := Nat
abbrev Constructor := Nat

inductive Value where
  | unit
  | boolean (value : Bool)
  | integer (value : Int)
  | context
  | tag (constructor : Constructor)
  | request (fields : Nat)
  | storage (location fields : Nat)
  | location (address : Nat)
  | function (address : Nat)
  | closureCode (node : NodeId)
  deriving DecidableEq

inductive Pattern where
  | binder (name : Binder)
  | wildcard
  | unit
  | boolean (value : Bool)
  | tuple (fields : List Pattern)
  | constructor (name : Constructor) (payload : Option Pattern)

inductive Node where
  | unit
  | boolean (value : Bool)
  | integer (value : Int)
  | caseMatch (scrutinee : NodeId) (arms : List (Pattern × NodeId))
  | integerEqual (left right : NodeId)
  | integerAdd (api : Nat) (context left right : NodeId)
  | apply (function argument : NodeId)
  | recursiveBind (members : List (Binder × NodeId)) (body : NodeId)
  | closure (context : NodeId) (captures : List NodeId) (storage : NodeId)
      (parameter : Binder) (body : NodeId)
  | variable (binder : Binder)
  | bind (binder : Binder) (initializer body : NodeId)
  | query (operand : NodeId)
  | request (fields : Nat)
  | allocate (context request : NodeId)
  | tuple (constructor : Option Constructor) (context : NodeId)
      (fields : List NodeId) (storage : NodeId)

abbrev Program := NodeId → Option Node
abbrev Environment := List (Binder × Value)
abbrev Store := State Value

/-- The existing integer representation has an immediate signed-i128 case. -/
def Immediate (value : Int) : Prop := -(2 ^ 127 : Int) ≤ value ∧ value < (2 ^ 127 : Int)

/-- Normal addition either returns immediately or uses fresh initialized backing. -/
inductive BufferReturn : Value → Value → Bool → Bool → Store → Value → Store → Prop where
  | immediate (left right : Int) (storageAvailable : Bool) (state : Store)
      (fits : Immediate (left + right)) :
      BufferReturn (.integer left) (.integer right) true storageAvailable state
        (.integer (left + right)) state
  | backed (left right : Int) (state afterAlloc finish : Store) (location : Nat)
      (bytes : List Value) (notFits : ¬ Immediate (left + right)) (nonempty : bytes ≠ [])
      (allocated : allocate .hostDefault bytes.length true state = some (location, afterAlloc))
      (initialized : initializeStorage location bytes.length bytes afterAlloc = some (bytes, finish)) :
      BufferReturn (.integer left) (.integer right) true true state
        (.integer (left + right)) finish

def storedFields (constructor : Option Constructor) (values : List Value) : List Value :=
  match constructor with
  | none => values
  | some tag => .tag tag :: values

def lookup (environment : Environment) (binder : Binder) : Option Value :=
  (environment.find? fun binding => binding.1 == binder).map Prod.snd

def extend (environment : Environment) (binder : Binder) (value : Value) : Environment :=
  (binder, value) :: environment

/-- Read the latest initialized value-array at a returned location. -/
def readCell (store : Store) (location : Nat) : Option (List Value) :=
  (store.cells.find? fun cell => cell.1 == location).map Prod.snd

/-- A successful cell read identifies a live stored-cell entry. -/
theorem readCell_member (store : Store) (address : Nat) (values : List Value)
    (read : readCell store address = some values) : (address, values) ∈ store.cells := by
  unfold readCell at read
  cases found : store.cells.find? (fun cell => cell.1 == address) with
  | none => simp [found] at read
  | some item =>
    have member := List.mem_of_find?_eq_some found
    have matchingKey := List.find?_some found
    rcases item with ⟨key, contents⟩
    simp only [beq_iff_eq] at matchingKey
    subst key
    simp [found] at read
    subst contents
    exact member

/-- Actual heap access follows zero or more initialized recursive aliases. -/
def readAlias (store : Store) (location : Nat) : Option Nat :=
  (store.aliases.find? fun cell => cell.1 == location).map Prod.snd

/-- A successful alias read identifies an installed alias entry. -/
theorem readAlias_member (store : Store) (address target : Nat)
    (read : readAlias store address = some target) : (address, target) ∈ store.aliases := by
  unfold readAlias at read
  cases found : store.aliases.find? (fun cell => cell.1 == address) with
  | none => simp [found] at read
  | some item =>
    have member := List.mem_of_find?_eq_some found
    have matchingKey := List.find?_some found
    rcases item with ⟨key, destination⟩
    simp only [beq_iff_eq] at matchingKey
    subst key
    simp [found] at read
    subst destination
    exact member

/-- The next fresh location is not an installed recursive alias. -/
theorem bounded_fresh_no_alias (store : Store) (bounded : BoundedLocations store) :
    readAlias store store.nextLocation = none := by
  cases read : readAlias store store.nextLocation with
  | none => rfl
  | some target =>
    have member := readAlias_member store store.nextLocation target read
    have less := bounded.2.2.2 store.nextLocation target member
    omega

/-- Only finite chains ending at initialized storage yield a normal access. -/
inductive Resolve (store : Store) : Nat → Nat → Prop where
  | cell (location : Nat) (values : List Value)
      (notAlias : readAlias store location = none)
      (present : readCell store location = some values) : Resolve store location location
  | alias (location target resolved : Nat)
      (link : readAlias store location = some target)
      (rest : Resolve store target resolved) : Resolve store location resolved

/-- A successful heap lookup has one resolved location. -/
theorem resolve_deterministic {store : Store} {address first second : Nat}
    (left : Resolve store address first) (right : Resolve store address second) : first = second := by
  induction left generalizing second with
  | cell location values notAlias present =>
    cases right with
    | cell => rfl
    | alias _ _ _ link _ => simp_all
  | alias location target resolved link rest ih =>
    cases right with
    | cell _ _ notAlias _ => simp_all
    | alias _ other result otherLink otherRest =>
      have same : target = other := by simpa [link] using otherLink
      subst other
      exact ih otherRest

/-- Unchanged alias links and retained cells preserve an existing resolution. -/
theorem resolve_preserved {before after : Store} {address resolved : Nat}
    (aliasesSame : after.aliases = before.aliases)
    (cellsRetained : ∀ location values, readCell before location = some values →
      readCell after location = some values)
    (resolution : Resolve before address resolved) : Resolve after address resolved := by
  induction resolution with
  | cell location values notAlias present =>
    apply Resolve.cell location values
    · simpa [readAlias, aliasesSame] using notAlias
    · exact cellsRetained location values present
  | alias location target resolved link rest ih =>
    apply Resolve.alias location target resolved
    · simpa [readAlias, aliasesSame] using link
    · exact ih

/-- The selected default query preserves existing heap resolutions. -/
theorem query_preserves_resolution {before after : Store} {address resolved : Nat}
    (queryStep : query .hostDefault before = some (.hostDefault, after))
    (resolution : Resolve before address resolved) : Resolve after address resolved := by
  simp only [query, Option.some.injEq, Prod.mk.injEq] at queryStep
  rcases queryStep with ⟨_, rfl⟩
  apply resolve_preserved (by rfl) _ resolution
  intro location values read
  simpa [readCell] using read

/-- The selected default query preserves an existing initialized cell. -/
theorem query_preserves_cell {before after : Store} {address : Nat} {values : List Value}
    (queryStep : query .hostDefault before = some (.hostDefault, after))
    (cell : readCell before address = some values) : readCell after address = some values := by
  simp only [query, Option.some.injEq, Prod.mk.injEq] at queryStep
  rcases queryStep with ⟨_, rfl⟩
  simpa [readCell] using cell

/-- Independently resolved reads of the same location return the same fields. -/
theorem resolved_fields_unique {store : Store} {address first second : Nat}
    {left right : List Value} (leftResolution : Resolve store address first)
    (rightResolution : Resolve store address second)
    (leftRead : readCell store first = some left) (rightRead : readCell store second = some right) :
    left = right := by
  have same := resolve_deterministic leftResolution rightResolution
  subst second
  simp_all

/-- The runtime's stored-field view distinguishes tuples from nominal values. -/
def tupleFields : List Value → Option (List Value)
  | .tag _ :: _ | .closureCode _ :: _ => none
  | values => some values

/-- The runtime accepts exactly a nominal tag and its optional single payload. -/
def constructorFields : List Value → Option (Constructor × Option Value)
  | [.tag tag] => some (tag, none)
  | [.tag tag, payload] => some (tag, some payload)
  | _ => none

mutual
  /-- A normal pattern attempt produces bindings on success and `none` on miss. -/
  inductive Attempt (store : Store) : Pattern → Value → Option Environment → Prop where
    | binder (name : Binder) (value : Value) :
        Attempt store (.binder name) value (some [(name, value)])
    | wildcard (value : Value) : Attempt store .wildcard value (some [])
    | unitHit : Attempt store .unit .unit (some [])
    | unitMiss (value : Value) (different : value ≠ .unit) :
        Attempt store .unit value none
    | booleanHit (value : Bool) : Attempt store (.boolean value) (.boolean value) (some [])
    | booleanMiss (expected : Bool) (value : Value) (different : value ≠ .boolean expected) :
        Attempt store (.boolean expected) value none
    | tupleNotLocation (patterns : List Pattern) (value : Value)
        (notLocation : ∀ address, value ≠ .location address) :
        Attempt store (.tuple patterns) value none
    | tupleWrongKind (patterns : List Pattern) (address resolved : Nat) (stored : List Value)
        (resolution : Resolve store address resolved) (read : readCell store resolved = some stored) (wrong : tupleFields stored = none) :
        Attempt store (.tuple patterns) (.location address) none
    | tupleFields (patterns : List Pattern) (address resolved : Nat) (stored values : List Value)
        (result : Option Environment) (resolution : Resolve store address resolved)
        (read : readCell store resolved = some stored)
        (view : tupleFields stored = some values)
        (attempt : FieldAttempts store patterns values result) :
        Attempt store (.tuple patterns) (.location address) result
    | constructorNotLocation (name : Constructor) (payload : Option Pattern) (value : Value)
        (notLocation : ∀ address, value ≠ .location address) :
        Attempt store (.constructor name payload) value none
    | constructorWrongKind (name : Constructor) (payload : Option Pattern)
        (address resolved : Nat) (stored : List Value) (resolution : Resolve store address resolved)
        (read : readCell store resolved = some stored)
        (wrong : constructorFields stored = none) :
        Attempt store (.constructor name payload) (.location address) none
    | constructorWrongTag (name found : Constructor) (payload : Option Pattern)
        (address resolved : Nat) (stored : List Value) (actual : Option Value)
        (resolution : Resolve store address resolved) (read : readCell store resolved = some stored)
        (view : constructorFields stored = some (found, actual)) (different : found ≠ name) :
        Attempt store (.constructor name payload) (.location address) none
    | constructorNoPayload (name : Constructor) (address resolved : Nat) (stored : List Value)
        (resolution : Resolve store address resolved) (read : readCell store resolved = some stored)
        (view : constructorFields stored = some (name, none)) :
        Attempt store (.constructor name none) (.location address) (some [])
    | constructorPayload (name : Constructor) (pattern : Pattern) (address resolved : Nat)
        (stored : List Value) (value : Value) (result : Option Environment)
        (resolution : Resolve store address resolved) (read : readCell store resolved = some stored)
        (view : constructorFields stored = some (name, some value))
        (attempt : Attempt store pattern value result) :
        Attempt store (.constructor name (some pattern)) (.location address) result
    | constructorMissingPayload (name : Constructor) (pattern : Pattern) (address resolved : Nat)
        (stored : List Value) (resolution : Resolve store address resolved)
        (read : readCell store resolved = some stored)
        (view : constructorFields stored = some (name, none)) :
        Attempt store (.constructor name (some pattern)) (.location address) none
    | constructorUnexpectedPayload (name : Constructor) (address resolved : Nat)
        (stored : List Value) (value : Value) (resolution : Resolve store address resolved)
        (read : readCell store resolved = some stored)
        (view : constructorFields stored = some (name, some value)) :
        Attempt store (.constructor name none) (.location address) none

  /-- Exact arity and ordered subpattern attempts for an ordinary tuple. -/
  inductive FieldAttempts (store : Store) : List Pattern → List Value → Option Environment → Prop where
    | empty : FieldAttempts store [] [] (some [])
    | extraPatterns (pattern : Pattern) (patterns : List Pattern) :
        FieldAttempts store (pattern :: patterns) [] none
    | extraValues (value : Value) (values : List Value) :
        FieldAttempts store [] (value :: values) none
    | headMiss (pattern : Pattern) (patterns : List Pattern) (value : Value) (values : List Value)
        (miss : Attempt store pattern value none) :
        FieldAttempts store (pattern :: patterns) (value :: values) none
    | tailMiss (pattern : Pattern) (patterns : List Pattern) (value : Value) (values : List Value)
        (bindings : Environment) (hit : Attempt store pattern value (some bindings))
        (miss : FieldAttempts store patterns values none) :
        FieldAttempts store (pattern :: patterns) (value :: values) none
    | hit (pattern : Pattern) (patterns : List Pattern) (value : Value) (values : List Value)
        (headBindings tailBindings : Environment)
        (head : Attempt store pattern value (some headBindings))
        (tail : FieldAttempts store patterns values (some tailBindings)) :
        FieldAttempts store (pattern :: patterns) (value :: values) (some (headBindings ++ tailBindings))
end

/-- Arms are tested in source order; only prior misses permit a later arm. -/
inductive Selected (store : Store) (value : Value) :
    List (Pattern × NodeId) → NodeId → Environment → Prop where
  | first (pattern : Pattern) (body : NodeId) (rest : List (Pattern × NodeId))
      (bindings : Environment) (hit : Attempt store pattern value (some bindings)) :
      Selected store value ((pattern, body) :: rest) body bindings
  | later (pattern : Pattern) (body : NodeId) (rest : List (Pattern × NodeId))
      (selected : NodeId) (bindings : Environment)
      (miss : Attempt store pattern value none)
      (next : Selected store value rest selected bindings) :
      Selected store value ((pattern, body) :: rest) selected bindings


/-- Exact binder/operand pairs used when reopening a stored Core closure. -/
inductive CaptureBindings (program : Program) : List NodeId → List Value → Environment → Prop where
  | empty : CaptureBindings program [] [] []
  | cons (node : NodeId) (nodes : List NodeId) (name : Binder) (value : Value)
      (values : List Value) (rest : Environment)
      (shape : program node = some (.variable name))
      (tail : CaptureBindings program nodes values rest) :
      CaptureBindings program (node :: nodes) (value :: values) ((name, value) :: rest)

/-- A callable is reopened from its resolved storage and original code node. -/
inductive CallTarget (program : Program) (store : Store) : Value → Binder → NodeId → Environment → Prop where
  | stored (callable : Value) (address resolved code context storage : NodeId)
      (captures : List NodeId) (parameter : Binder) (body : NodeId)
      (captured : List Value) (bindings : Environment)
      (callableAddress : callable = .location address ∨ callable = .function address)
      (resolution : Resolve store address resolved)
      (fields : readCell store resolved = some (.closureCode code :: captured))
      (shape : program code = some (.closure context captures storage parameter body))
      (captureBindings : CaptureBindings program captures captured bindings) :
      CallTarget program store callable parameter body bindings.reverse

/-- Reserve all recursive slots before evaluating any initializer. -/
inductive ReserveMembers : List (Binder × NodeId) → Store → Environment → List (Nat × NodeId) → Store → Prop where
  | empty (store : Store) : ReserveMembers [] store [] [] store
  | cons (name : Binder) (initial : NodeId) (rest : List (Binder × NodeId))
      (before middle finish : Store) (slot : Nat) (bindings : Environment)
      (pending : List (Nat × NodeId))
      (reserved : reserveRecursive before = (slot, middle))
      (remaining : ReserveMembers rest middle bindings pending finish) :
      ReserveMembers ((name, initial) :: rest) before ((name, .location slot) :: bindings)
        ((slot, initial) :: pending) finish

mutual
  /-- Normal strict evaluations; refusal and unsupported nodes have no rule. -/
  inductive Eval (program : Program) : Environment → NodeId → Store → Value → Store → Prop where
    | unit {env node state} (shape : program node = some .unit) :
        Eval program env node state .unit state
    | boolean {env node state value} (shape : program node = some (.boolean value)) :
        Eval program env node state (.boolean value) state
    | integer {env node state value} (shape : program node = some (.integer value)) :
        Eval program env node state (.integer value) state
    | variable {env node state binder value} (shape : program node = some (.variable binder))
        (binding : lookup env binder = some value) : Eval program env node state value state
    | caseMatch {env node scrutinee arms state afterScrutinee final value body bindings result}
        (shape : program node = some (.caseMatch scrutinee arms))
        (scrutineeEval : Eval program env scrutinee state value afterScrutinee)
        (chosen : Selected afterScrutinee value arms body bindings)
        (bodyEval : Eval program (bindings.reverse ++ env) body afterScrutinee result final) :
        Eval program env node state result final
    | integerEqual {env node left right state afterLeft final first second}
        (shape : program node = some (.integerEqual left right))
        (leftEval : Eval program env left state (.integer first) afterLeft)
        (rightEval : Eval program env right afterLeft (.integer second) final) :
        Eval program env node state (.boolean (decide (first = second))) final
    | integerAdd {env node api context left right state afterContext afterLeft afterRight final
        first second result workAvailable storageAvailable}
        (shape : program node = some (.integerAdd api context left right))
        (contextEval : Eval program env context state .context afterContext)
        (leftEval : Eval program env left afterContext first afterLeft)
        (rightEval : Eval program env right afterLeft second afterRight)
        (returned : BufferReturn first second workAvailable storageAvailable afterRight result final) :
        Eval program env node state result final
    | apply {env node function argument state afterFunction afterArgument final
        callable value parameter body captured result}
        (shape : program node = some (.apply function argument))
        (functionEval : Eval program env function state callable afterFunction)
        (target : CallTarget program afterFunction callable parameter body captured)
        (argumentEval : Eval program env argument afterFunction value afterArgument)
        (bodyEval : Eval program (extend captured parameter value) body afterArgument result final) :
        Eval program env node state result final
    | recursiveBind {env node members body state afterReserve afterInitialize final
        bindings pending result}
        (shape : program node = some (.recursiveBind members body))
        (nonempty : members ≠ [])
        (distinct : (members.map Prod.fst).Nodup)
        (reserved : ReserveMembers members state bindings pending afterReserve)
        (initialized : InitializeRecursive program (bindings.reverse ++ env) pending afterReserve afterInitialize)
        (bodyEval : Eval program (bindings.reverse ++ env) body afterInitialize result final) :
        Eval program env node state result final
    | closure {env node context captures storage parameter body state afterContext afterCaptures
        afterStorage final values location count}
        (shape : program node = some (.closure context captures storage parameter body))
        (contextEval : Eval program env context state .context afterContext)
        (captureEvals : EvalFields program env captures afterContext values afterCaptures)
        (storageEval : Eval program env storage afterCaptures (.storage location count) afterStorage)
        (initialized : initializeStorage location count (.closureCode node :: values) afterStorage =
          some (.closureCode node :: values, final)) :
        Eval program env node state (.function location) final
    | bind {env node state afterInit result final binder initial body value}
        (shape : program node = some (.bind binder initial body))
        (initialEval : Eval program env initial state value afterInit)
        (bodyEval : Eval program (extend env binder value) body afterInit result final) :
        Eval program env node state result final
    | query {env node operand state afterOperand final chosen}
        (shape : program node = some (.query operand))
        (operandEval : Eval program env operand state .unit afterOperand)
        (selected : query .hostDefault afterOperand = some (chosen, final)) :
        Eval program env node state .context final
    | request {env node state fields} (shape : program node = some (.request fields)) :
        Eval program env node state (.request fields) state
    | allocate {env node context request state afterContext afterRequest final fields location}
        (shape : program node = some (.allocate context request))
        (contextEval : Eval program env context state .context afterContext)
        (requestEval : Eval program env request afterContext (.request fields) afterRequest)
        (allocated : allocate .hostDefault fields true afterRequest = some (location, final)) :
        Eval program env node state (.storage location fields) final
    | tuple {env node constructor context fields storage state afterContext afterFields afterStorage final
        values location count}
        (shape : program node = some (.tuple constructor context fields storage))
        (contextEval : Eval program env context state .context afterContext)
        (fieldEvals : EvalFields program env fields afterContext values afterFields)
        (storageEval : Eval program env storage afterFields (.storage location count) afterStorage)
        (initialized : initializeStorage location count
          (storedFields constructor values) afterStorage =
            some (storedFields constructor values, final)) :
        Eval program env node state (.location location) final

  /-- Core evaluates every explicit tuple field in source order. -/
  inductive EvalFields (program : Program) : Environment → List NodeId → Store → List Value → Store → Prop where
    | nil {env state} : EvalFields program env [] state [] state
    | cons {env node nodes start middle finish value values}
        (head : Eval program env node start value middle)
        (tail : EvalFields program env nodes middle values finish) :
        EvalFields program env (node :: nodes) start (value :: values) finish

  /-- Each initializer runs in the shared recursive environment, then installs its alias. -/
  inductive InitializeRecursive (program : Program) : Environment → List (Nat × NodeId) → Store → Store → Prop where
    | empty {env state} : InitializeRecursive program env [] state state
    | location {env slot initial rest start afterValue afterAlias finish target}
        (evaluation : Eval program env initial start (.location target) afterValue)
        (installed : initializeAlias slot target afterValue = some afterAlias)
        (remaining : InitializeRecursive program env rest afterAlias finish) :
        InitializeRecursive program env ((slot, initial) :: rest) start finish
    | function {env slot initial rest start afterValue afterAlias finish target}
        (evaluation : Eval program env initial start (.function target) afterValue)
        (installed : initializeAlias slot target afterValue = some afterAlias)
        (remaining : InitializeRecursive program env rest afterAlias finish) :
        InitializeRecursive program env ((slot, initial) :: rest) start finish
end

/-- Exactly the node links tested by the restricted tuple recognizer. -/
structure CheckedTuple (program : Program) (root : NodeId) (constructor : Option Constructor)
    (fields : List NodeId) where
  contextBinder : Binder
  queryNode : NodeId
  unitNode : NodeId
  tupleNode : NodeId
  contextNode : NodeId
  storageNode : NodeId
  storageContextNode : NodeId
  requestNode : NodeId
  rootShape : program root = some (.bind contextBinder queryNode tupleNode)
  queryShape : program queryNode = some (.query unitNode)
  unitShape : program unitNode = some .unit
  tupleShape : program tupleNode = some (.tuple constructor contextNode fields storageNode)
  contextShape : program contextNode = some (.variable contextBinder)
  storageShape : program storageNode = some (.allocate storageContextNode requestNode)
  storageContextShape : program storageContextNode = some (.variable contextBinder)
  requestShape : program requestNode = some (.request (fields.length + constructor.toList.length))

/-- A checked Unit node cannot return another value or change the store. -/
theorem unit_inversion {program : Program} {node : NodeId} {env : Environment}
    {before after : Store} {value : Value} (shape : program node = some .unit)
    (evaluation : Eval program env node before value after) : value = .unit ∧ after = before := by
  cases evaluation <;> simp_all

/-- A checked Boolean literal returns its exact value without changing the store. -/
theorem boolean_inversion {program : Program} {node : NodeId} {env : Environment}
    {before after : Store} {result : Value} {value : Bool}
    (shape : program node = some (.boolean value))
    (evaluation : Eval program env node before result after) :
    result = .boolean value ∧ after = before := by
  cases evaluation <;> simp_all

/-- A checked variable reads the exact binder and performs no operation. -/
theorem variable_inversion {program : Program} {node : NodeId} {env : Environment}
    {before after : Store} {value : Value} {binder : Binder}
    (shape : program node = some (.variable binder))
    (evaluation : Eval program env node before value after) :
    lookup env binder = some value ∧ after = before := by
  cases evaluation <;> simp_all

/-- A checked request returns its exact layout without changing the store. -/
theorem request_inversion {program : Program} {node : NodeId} {env : Environment}
    {before after : Store} {value : Value} {fields : Nat}
    (shape : program node = some (.request fields))
    (evaluation : Eval program env node before value after) :
    value = .request fields ∧ after = before := by
  cases evaluation <;> simp_all

/-- The emitted binder shadows its prior environment with the returned context. -/
theorem lookup_extended (env : Environment) (binder : Binder) :
    lookup (extend env binder .context) binder = some .context := by
  simp [lookup, extend]

/-- A checked application resolves the callable before evaluating its argument. -/
theorem apply_inversion {program : Program} {node function argument : NodeId}
    {env : Environment} {before after : Store} {result : Value}
    (shape : program node = some (.apply function argument))
    (evaluation : Eval program env node before result after) :
    ∃ afterFunction afterArgument callable value parameter body captured,
      Eval program env function before callable afterFunction ∧
      CallTarget program afterFunction callable parameter body captured ∧
      Eval program env argument afterFunction value afterArgument ∧
      Eval program (extend captured parameter value) body afterArgument result after := by
  cases evaluation with
  | apply actual functionEval target argumentEval bodyEval =>
    have same := Option.some.inj (shape.symm.trans actual)
    simp only [Node.apply.injEq] at same
    rcases same with ⟨rfl, rfl⟩
    exact ⟨_, _, _, _, _, _, _, functionEval, target, argumentEval, bodyEval⟩
  | _ => simp_all

/-- Strict integer equality uses the exact two evaluated operands. -/
theorem integer_equal_inversion {program : Program} {node left right : NodeId}
    {env : Environment} {before after : Store} {result : Value}
    (shape : program node = some (.integerEqual left right))
    (evaluation : Eval program env node before result after) :
    ∃ middle, ∃ first second : Int,
      Eval program env left before (.integer first) middle ∧
      Eval program env right middle (.integer second) after ∧
      result = .boolean (decide (first = second)) := by
  cases evaluation with
  | integerEqual actual leftEval rightEval =>
    have same := Option.some.inj (shape.symm.trans actual)
    simp only [Node.integerEqual.injEq] at same
    rcases same with ⟨rfl, rfl⟩
    exact ⟨_, _, _, leftEval, rightEval, rfl⟩
  | _ => simp_all

/-- Match evaluates its actual scrutinee and chooses the first successful arm. -/
theorem case_match_inversion {program : Program} {node scrutinee : NodeId}
    {arms : List (Pattern × NodeId)} {env : Environment} {before after : Store} {result : Value}
    (shape : program node = some (.caseMatch scrutinee arms))
    (evaluation : Eval program env node before result after) :
    ∃ middle value body bindings,
      Eval program env scrutinee before value middle ∧ Selected middle value arms body bindings ∧
      Eval program (bindings.reverse ++ env) body middle result after := by
  cases evaluation with
  | caseMatch actual scrutineeEval chosen bodyEval =>
    have same := Option.some.inj (shape.symm.trans actual)
    simp only [Node.caseMatch.injEq] at same
    rcases same with ⟨rfl, rfl⟩
    exact ⟨_, _, _, _, scrutineeEval, chosen, bodyEval⟩
  | _ => simp_all

/-- Two fields are evaluated strictly from left to right. -/
theorem pair_fields_inversion {program : Program} {env : Environment} {left right : NodeId}
    {before after : Store} {values : List Value}
    (evaluation : EvalFields program env [left, right] before values after) :
    ∃ middle leftValue rightValue,
      Eval program env left before leftValue middle ∧ Eval program env right middle rightValue after ∧
      values = [leftValue, rightValue] := by
  cases evaluation with
  | cons first tail =>
    cases tail with
    | cons second tail =>
      cases tail
      exact ⟨_, _, _, first, second, rfl⟩

/-- A fresh context binder leaves any different field binder unchanged. -/
theorem lookup_extended_other (env : Environment) (contextBinder fieldBinder : Binder)
    (different : fieldBinder ≠ contextBinder) :
    lookup (extend env contextBinder .context) fieldBinder = lookup env fieldBinder := by
  simp [lookup, extend, Ne.symm different]

/-- Two checked variable fields preserve their order and do not change storage. -/
theorem variable_pair_fields {program : Program} {env : Environment} {left right : NodeId}
    {leftName rightName : Binder} {leftValue rightValue : Value} {before after : Store}
    {values : List Value}
    (leftShape : program left = some (.variable leftName))
    (rightShape : program right = some (.variable rightName))
    (leftBinding : lookup env leftName = some leftValue)
    (rightBinding : lookup env rightName = some rightValue)
    (evaluation : EvalFields program env [left, right] before values after) :
    values = [leftValue, rightValue] ∧ after = before := by
  cases evaluation with
  | cons first tail =>
    obtain ⟨firstFound, firstStore⟩ := variable_inversion leftShape first
    simp only [leftBinding, Option.some.injEq] at firstFound
    cases firstFound
    cases firstStore
    cases tail with
    | cons second tail =>
      obtain ⟨secondFound, secondStore⟩ := variable_inversion rightShape second
      simp only [rightBinding, Option.some.injEq] at secondFound
      cases secondFound
      cases secondStore
      cases tail
      exact ⟨rfl, rfl⟩

/-- Normal evaluation of a checked bind first evaluates its initializer. -/
theorem bind_inversion {program : Program} {node : NodeId} {env : Environment}
    {before after : Store} {result : Value} {binder : Binder} {initial body : NodeId}
    (shape : program node = some (.bind binder initial body))
    (evaluation : Eval program env node before result after) :
    ∃ middle value, Eval program env initial before value middle ∧
      Eval program (extend env binder value) body middle result after := by
  cases evaluation with
  | bind shapeNode initialEval bodyEval =>
    have same := Option.some.inj (shape.symm.trans shapeNode)
    simp only [Node.bind.injEq] at same
    rcases same with ⟨rfl, rfl, rfl⟩
    exact ⟨_, _, initialEval, bodyEval⟩
  | _ => simp_all

/-- Normal Add evaluates the actual context and operands before its return. -/
theorem integer_add_inversion {program : Program} {node context left right : NodeId} {api : Nat}
    {env : Environment} {before after : Store} {result : Value}
    (shape : program node = some (.integerAdd api context left right))
    (evaluation : Eval program env node before result after) :
    ∃ afterContext afterLeft afterRight first second workAvailable storageAvailable,
      Eval program env context before .context afterContext ∧
      Eval program env left afterContext first afterLeft ∧
      Eval program env right afterLeft second afterRight ∧
      BufferReturn first second workAvailable storageAvailable afterRight result after := by
  cases evaluation with
  | integerAdd actual contextEval leftEval rightEval returned =>
    have same := Option.some.inj (shape.symm.trans actual)
    simp only [Node.integerAdd.injEq] at same
    rcases same with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨_, _, _, _, _, _, _, contextEval, leftEval, rightEval, returned⟩
  | _ => simp_all

/-- A checked query evaluates its Unit operand before resuming the provider. -/
theorem query_inversion {program : Program} {node operand : NodeId} {env : Environment}
    {before after : Store} {result : Value}
    (shape : program node = some (.query operand))
    (evaluation : Eval program env node before result after) :
    result = .context ∧ ∃ middle chosen,
      Eval program env operand before .unit middle ∧
      query .hostDefault middle = some (chosen, after) := by
  cases evaluation with
  | query shapeNode operandEval selected =>
    have same := Option.some.inj (shape.symm.trans shapeNode)
    simp only [Node.query.injEq] at same
    rcases same with rfl
    exact ⟨rfl, _, _, operandEval, selected⟩
  | _ => simp_all

/-- Tuple evaluation obtains context, evaluates fields, then storage. -/
theorem tuple_inversion {program : Program} {node context storage : NodeId}
    {constructor : Option Constructor} {fields : List NodeId} {env : Environment}
    {before after : Store} {result : Value}
    (shape : program node = some (.tuple constructor context fields storage))
    (evaluation : Eval program env node before result after) :
    ∃ afterContext afterFields afterStorage location count values,
      Eval program env context before .context afterContext ∧
      EvalFields program env fields afterContext values afterFields ∧
      Eval program env storage afterFields (.storage location count) afterStorage ∧
      initializeStorage location count
        (storedFields constructor values) afterStorage =
          some (storedFields constructor values, after) ∧
      result = .location location := by
  cases evaluation with
  | tuple shapeNode contextEval fieldEvals storageEval initialized =>
    have same := Option.some.inj (shape.symm.trans shapeNode)
    simp only [Node.tuple.injEq] at same
    rcases same with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨_, _, _, _, _, _, contextEval, fieldEvals, storageEval, initialized, rfl⟩
  | _ => simp_all

/-- Allocation evaluates its context and request before invoking the provider. -/
theorem allocate_inversion {program : Program} {node context request : NodeId}
    {env : Environment} {before after : Store} {result : Value}
    (shape : program node = some (.allocate context request))
    (evaluation : Eval program env node before result after) :
    ∃ afterContext afterRequest fields location,
      Eval program env context before .context afterContext ∧
      Eval program env request afterContext (.request fields) afterRequest ∧
      allocate .hostDefault fields true afterRequest = some (location, after) ∧
      result = .storage location fields := by
  cases evaluation with
  | allocate shapeNode contextEval requestEval allocated =>
    have same := Option.some.inj (shape.symm.trans shapeNode)
    simp only [Node.allocate.injEq] at same
    rcases same with ⟨rfl, rfl⟩
    exact ⟨_, _, _, _, contextEval, requestEval, allocated, rfl⟩
  | _ => simp_all

/-- Inversion of the graph-bound tuple exposes its strict execution stages. -/
theorem checked_tuple_inversion {program : Program} {root : NodeId}
    {constructor : Option Constructor} {fields : List NodeId} {env : Environment}
    {start finish : Store} {result : Value}
    (checked : CheckedTuple program root constructor fields)
    (evaluation : Eval program env root start result finish) :
    ∃ queried afterFields afterAlloc location values,
      query .hostDefault start = some (.hostDefault, queried) ∧
      EvalFields program (extend env checked.contextBinder .context) fields queried values afterFields ∧
      allocate .hostDefault (fields.length + constructor.toList.length) true afterFields =
        some (location, afterAlloc) ∧
      initializeStorage location (fields.length + constructor.toList.length)
        (storedFields constructor values) afterAlloc =
          some (storedFields constructor values, finish) ∧
      result = .location location := by
  obtain ⟨afterInit, initialValue, initialEval, bodyEval⟩ :=
    bind_inversion checked.rootShape evaluation
  obtain ⟨valueEq, afterOperand, chosen, operandEval, selected⟩ :=
    query_inversion checked.queryShape initialEval
  subst initialValue
  obtain ⟨_, operandState⟩ := unit_inversion checked.unitShape operandEval
  subst afterOperand
  have chosenHost := (query_projects start afterInit .hostDefault chosen selected).1
  subst chosen
  obtain ⟨afterContext, afterFields, afterStorage, location, count, values,
    contextEval, fieldEvals, storageEval, initialized, resultEq⟩ :=
      tuple_inversion checked.tupleShape bodyEval
  obtain ⟨_, contextState⟩ := variable_inversion checked.contextShape contextEval
  subst afterContext
  obtain ⟨afterStorageContext, afterRequest, requested, allocatedLocation,
    storageContextEval, requestEval, allocated, storageValue⟩ :=
      allocate_inversion checked.storageShape storageEval
  have storageShape : location = allocatedLocation ∧ count = requested := by
    simpa using storageValue
  rcases storageShape with ⟨locationEq, countEq⟩
  subst allocatedLocation
  subst requested
  obtain ⟨_, storageContextState⟩ :=
    variable_inversion checked.storageContextShape storageContextEval
  subst afterStorageContext
  obtain ⟨requestValue, requestState⟩ := request_inversion checked.requestShape requestEval
  subst afterRequest
  have layoutEq : count = fields.length + constructor.toList.length := by
    simpa using requestValue
  subst count
  exact ⟨afterInit, afterFields, afterStorage, location, values, selected, fieldEvals,
    allocated, initialized, resultEq⟩

/-- A checked two-variable tuple stores exactly the two bound operands. -/
theorem checked_variable_pair_tuple {program : Program} {root left right : NodeId}
    {env : Environment} {start finish : Store} {result leftValue rightValue : Value}
    (checked : CheckedTuple program root none [left, right])
    (leftName rightName : Binder)
    (leftShape : program left = some (.variable leftName))
    (rightShape : program right = some (.variable rightName))
    (leftFresh : leftName ≠ checked.contextBinder)
    (rightFresh : rightName ≠ checked.contextBinder)
    (leftBinding : lookup env leftName = some leftValue)
    (rightBinding : lookup env rightName = some rightValue)
    (evaluation : Eval program env root start result finish) :
    ∃ queried afterAlloc location,
      query .hostDefault start = some (.hostDefault, queried) ∧
      allocate .hostDefault 2 true queried = some (location, afterAlloc) ∧
      initializeStorage location 2 [leftValue, rightValue] afterAlloc =
        some ([leftValue, rightValue], finish) ∧ result = .location location := by
  obtain ⟨queried, afterFields, afterAlloc, location, values, queryStep, fieldEvals,
    allocated, initialized, resultEq⟩ := checked_tuple_inversion checked evaluation
  have leftExtended : lookup (extend env checked.contextBinder .context) leftName = some leftValue := by
    rw [lookup_extended_other env checked.contextBinder leftName leftFresh]
    exact leftBinding
  have rightExtended : lookup (extend env checked.contextBinder .context) rightName = some rightValue := by
    rw [lookup_extended_other env checked.contextBinder rightName rightFresh]
    exact rightBinding
  obtain ⟨sameValues, sameStore⟩ :=
    variable_pair_fields leftShape rightShape leftExtended rightExtended fieldEvals
  subst values
  subst afterFields
  exact ⟨queried, afterAlloc, location, queryStep, by simpa using allocated,
    by simpa [storedFields] using initialized, resultEq⟩

/-- Completing an ordered host pair preserves previously readable cells. -/
theorem host_pair_retains {start queried afterAlloc finish : Store} {location : Nat}
    {leftValue rightValue : Value} (bounded : BoundedLocations start)
    (queryStep : query .hostDefault start = some (.hostDefault, queried))
    (allocated : allocate .hostDefault 2 true queried = some (location, afterAlloc))
    (initialized : initializeStorage location 2 [leftValue, rightValue] afterAlloc =
      some ([leftValue, rightValue], finish)) :
    location = start.nextLocation ∧ readCell finish location = some [leftValue, rightValue] ∧
      finish.aliases = start.aliases ∧ BoundedLocations finish ∧
      (∀ address values, readCell start address = some values → readCell finish address = some values) := by
  have queryBound := query_preserves_bounded start queried .hostDefault .hostDefault bounded queryStep
  have allocationBound := allocation_preserves_bounded queried afterAlloc .hostDefault 2 true location
    queryBound allocated
  have finishBound := initialization_preserves_bounded afterAlloc finish location 2
    [leftValue, rightValue] [leftValue, rightValue] allocationBound initialized
  simp only [query, Option.some.injEq, Prod.mk.injEq] at queryStep
  rcases queryStep with ⟨_, rfl⟩
  simp only [allocate, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Option.some.injEq, Prod.mk.injEq] at allocated
  rcases allocated with ⟨rfl, rfl⟩
  simp only [initializeStorage] at initialized
  split at initialized
  · simp only [Option.some.injEq, Prod.mk.injEq] at initialized
    rcases initialized with ⟨_, rfl⟩
    refine ⟨rfl, ?_, rfl, finishBound, ?_⟩
    · simp [readCell]
    · intro address values read
      have member := readCell_member start address values read
      have less := bounded.2.1 address values member
      have different : start.nextLocation ≠ address := by omega
      simpa [readCell, different] using read
  · simp_all

/-- A checked pair retains all previously stored cells and alias links. -/
theorem checked_variable_pair_retains {program : Program} {root left right : NodeId}
    {env : Environment} {start finish : Store} {result leftValue rightValue : Value}
    (checked : CheckedTuple program root none [left, right])
    (leftName rightName : Binder)
    (leftShape : program left = some (.variable leftName))
    (rightShape : program right = some (.variable rightName))
    (leftFresh : leftName ≠ checked.contextBinder)
    (rightFresh : rightName ≠ checked.contextBinder)
    (leftBinding : lookup env leftName = some leftValue)
    (rightBinding : lookup env rightName = some rightValue)
    (bounded : BoundedLocations start)
    (evaluation : Eval program env root start result finish) :
    ∃ location, location = start.nextLocation ∧ result = .location location ∧
      readCell finish location = some [leftValue, rightValue] ∧ finish.aliases = start.aliases ∧
      BoundedLocations finish ∧
      (∀ address values, readCell start address = some values → readCell finish address = some values) := by
  obtain ⟨queried, afterAlloc, location, queryStep, allocated, initialized, resultEq⟩ :=
    checked_variable_pair_tuple checked leftName rightName leftShape rightShape leftFresh rightFresh
      leftBinding rightBinding evaluation
  have queryBound := query_preserves_bounded start queried .hostDefault .hostDefault bounded queryStep
  have allocationBound := allocation_preserves_bounded queried afterAlloc .hostDefault 2 true location
    queryBound allocated
  have finishBound := initialization_preserves_bounded afterAlloc finish location 2
    [leftValue, rightValue] [leftValue, rightValue] allocationBound initialized
  simp only [query, Option.some.injEq, Prod.mk.injEq] at queryStep
  rcases queryStep with ⟨_, rfl⟩
  simp only [allocate, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Option.some.injEq, Prod.mk.injEq] at allocated
  rcases allocated with ⟨rfl, rfl⟩
  simp only [initializeStorage] at initialized
  split at initialized
  · simp only [Option.some.injEq, Prod.mk.injEq] at initialized
    rcases initialized with ⟨_, rfl⟩
    refine ⟨start.nextLocation, rfl, resultEq, ?_, rfl, finishBound, ?_⟩
    · simp [readCell]
    · intro address values read
      have member := readCell_member start address values read
      have less := bounded.2.1 address values member
      have different : start.nextLocation ≠ address := by omega
      simpa [readCell, different] using read
  · simp_all

/-- A checked tuple's actual stages establish the projected query and finish. -/
theorem checked_tuple_projects {program : Program} {root : NodeId}
    {constructor : Option Constructor} {fields : List NodeId} {env : Environment}
    {start finish : Store} {result : Value}
    (checked : CheckedTuple program root constructor fields)
    (evaluation : Eval program env root start result finish) :
    ∃ queried afterFields location values,
      CoreRemoval.Query .hostDefault (project start) .hostDefault (project queried) ∧
      EvalFields program (extend env checked.contextBinder .context) fields queried values afterFields ∧
      CoreStrict.Finish .hostDefault (project afterFields) (project finish) ∧
      result = .location location ∧
      finish.cells = (location, storedFields constructor values) :: afterFields.cells := by
  obtain ⟨queried, afterFields, afterAlloc, location, values, queryStep, fieldEvals,
    allocated, initialized, resultEq⟩ := checked_tuple_inversion checked evaluation
  have queryProjected := query_corresponds start queried .hostDefault .hostDefault queryStep
  have allocationProjected := (allocation_projects afterFields afterAlloc .hostDefault
    (fields.length + constructor.toList.length) true location allocated)
  have initializedFacts := initialization_preserves afterAlloc finish location
    (fields.length + constructor.toList.length) (storedFields constructor values)
    (storedFields constructor values) initialized
  have finished : CoreStrict.Finish .hostDefault (project afterFields) (project finish) := by
    rw [initializedFacts.2.2.1]
    exact CoreStrict.Finish.host (project afterFields) (project afterAlloc) location allocationProjected.1
  exact ⟨queried, afterFields, location, values, queryProjected, fieldEvals,
    finished, resultEq, by simpa [allocationProjected.2.2.2] using initializedFacts.2.1⟩


/-- The returned location has the exact initialized raw cell and whole fields. -/
theorem checked_tuple_reads_fields {program : Program} {root : NodeId}
    {constructor : Option Constructor} {fields : List NodeId} {env : Environment}
    {start finish : Store} {result : Value}
    (checked : CheckedTuple program root constructor fields)
    (evaluation : Eval program env root start result finish) :
    ∃ location values, result = .location location ∧
      readCell finish location = some (storedFields constructor values) := by
  obtain ⟨queried, afterFields, location, values, _, _, _, resultEq, cells⟩ :=
    checked_tuple_projects checked evaluation
  refine ⟨location, values, resultEq, ?_⟩
  simp [readCell, cells]

end Ash.NetworkLedger.CoreEval
