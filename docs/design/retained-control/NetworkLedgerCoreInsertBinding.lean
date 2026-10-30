import NetworkLedgerCoreInsert

/-
A schema-specific, finite decoder for the actual linked insertion fragment.
The checked program must be produced from authenticated arena coordinates;
provider selection, initialized input and Rust-to-model correspondence remain
separate obligations. An unsuccessful check returns no judgment.
-/
namespace Ash.NetworkLedger.CoreInsertBinding
open Ash.NetworkLedger
open Ash.NetworkLedger.CoreRegion
open Ash.NetworkLedger.CoreEval
open Ash.NetworkLedger.CoreValues
open Ash.NetworkLedger.CoreInsert


structure TupleCoordinates where
  root : NodeId
  contextBinder : Binder
  queryNode : NodeId
  unitNode : NodeId
  tupleNode : NodeId
  contextNode : NodeId
  storageNode : NodeId
  storageContextNode : NodeId
  requestNode : NodeId

structure ClosureCoordinates where
  root : NodeId
  contextBinder : Binder
  queryNode : NodeId
  unitNode : NodeId
  closureNode : NodeId
  contextNode : NodeId
  storageNode : NodeId
  storageContextNode : NodeId
  requestNode : NodeId
  parameter : Binder
  body : NodeId

def bindShape (program : Program) (node : NodeId) (b : Binder) (q body : NodeId) : Option (PLift (program node = some (.bind b q body))) := by
  match actual : program node with
  | some (.bind ab aq ac) =>
    if same : ab = b ∧ aq = q ∧ ac = body then
      rcases same with ⟨rfl, rfl, rfl⟩
      exact some ⟨rfl⟩
    else exact none
  | _ => exact none

def queryShape (program : Program) (node : NodeId) (operand : NodeId) : Option (PLift (program node = some (.query operand))) := by
  match actual : program node with
  | some (.query aq) =>
    if same : aq = operand then
      subst_vars
      exact some ⟨rfl⟩
    else exact none
  | _ => exact none

def unitShape (program : Program) (node : NodeId)  : Option (PLift (program node = some (.unit))) := by
  match actual : program node with
  | some (.unit) =>
    exact some ⟨rfl⟩
  | _ => exact none

def tupleShape (program : Program) (node : NodeId) (tag : Option Constructor) (context : NodeId) (fields : List NodeId) (storage : NodeId) : Option (PLift (program node = some (.tuple tag context fields storage))) := by
  match actual : program node with
  | some (.tuple atag ac af ast) =>
    if same : atag = tag ∧ ac = context ∧ af = fields ∧ ast = storage then
      rcases same with ⟨rfl, rfl, rfl, rfl⟩
      exact some ⟨rfl⟩
    else exact none
  | _ => exact none

def variableShape (program : Program) (node : NodeId) (binder : Binder) : Option (PLift (program node = some (.variable binder))) := by
  match actual : program node with
  | some (.variable ab) =>
    if same : ab = binder then
      subst_vars
      exact some ⟨rfl⟩
    else exact none
  | _ => exact none

def allocateShape (program : Program) (node : NodeId) (context request : NodeId) : Option (PLift (program node = some (.allocate context request))) := by
  match actual : program node with
  | some (.allocate ac ar) =>
    if same : ac = context ∧ ar = request then
      rcases same with ⟨rfl, rfl⟩
      exact some ⟨rfl⟩
    else exact none
  | _ => exact none

def requestShape (program : Program) (node : NodeId) (count : Nat) : Option (PLift (program node = some (.request count))) := by
  match actual : program node with
  | some (.request ac) =>
    if same : ac = count then
      subst_vars
      exact some ⟨rfl⟩
    else exact none
  | _ => exact none

def closureShape (program : Program) (node : NodeId) (context : NodeId) (captures : List NodeId) (storage : NodeId) (parameter : Binder) (body : NodeId) : Option (PLift (program node = some (.closure context captures storage parameter body))) := by
  match actual : program node with
  | some (.closure ac av ast ap ab) =>
    if same : ac = context ∧ av = captures ∧ ast = storage ∧ ap = parameter ∧ ab = body then
      rcases same with ⟨rfl, rfl, rfl, rfl, rfl⟩
      exact some ⟨rfl⟩
    else exact none
  | _ => exact none

def applyShape (program : Program) (node : NodeId) (function argument : NodeId) : Option (PLift (program node = some (.apply function argument))) := by
  match actual : program node with
  | some (.apply af aa) =>
    if same : af = function ∧ aa = argument then
      rcases same with ⟨rfl, rfl⟩
      exact some ⟨rfl⟩
    else exact none
  | _ => exact none

def argumentMatchShape (program : Program) (node : NodeId) (scrutinee : NodeId) (a b : Binder) (body : NodeId) : Option (PLift (program node = some (.caseMatch scrutinee [(.tuple [.binder a, .binder b], body)]))) := by
  match actual : program node with
  | some (.caseMatch ascr [(.tuple [.binder aa, .binder ab], abody)]) =>
    if same : ascr = scrutinee ∧ aa = a ∧ ab = b ∧ abody = body then
      rcases same with ⟨rfl, rfl, rfl, rfl⟩
      exact some ⟨rfl⟩
    else exact none
  | _ => exact none

def listMatchShape (program : Program) (node : NodeId) (scrutinee : NodeId) (empty more : Constructor) (entry tail : Binder) (emptyBody moreBody : NodeId) : Option (PLift (program node = some (.caseMatch scrutinee [(.constructor empty none, emptyBody), (.constructor more (some (.tuple [.binder entry, .binder tail])), moreBody)]))) := by
  match actual : program node with
  | some (.caseMatch ascr [(.constructor ae none, aeb), (.constructor am (some (.tuple [.binder ah, .binder atail])), amb)]) =>
    if same : ascr = scrutinee ∧ ae = empty ∧ aeb = emptyBody ∧ am = more ∧ ah = entry ∧ atail = tail ∧ amb = moreBody then
      rcases same with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact some ⟨rfl⟩
    else exact none
  | _ => exact none

def checkTuple (program : Program) (x : TupleCoordinates) (constructor : Option Constructor) (fields : List NodeId) : Option (CheckedTuple program x.root constructor fields) := do
  let ⟨rootShape⟩ ← bindShape program x.root x.contextBinder x.queryNode x.tupleNode
  let ⟨queryShape⟩ ← queryShape program x.queryNode x.unitNode
  let ⟨unitShape⟩ ← unitShape program x.unitNode
  let ⟨tupleShape⟩ ← tupleShape program x.tupleNode constructor x.contextNode fields x.storageNode
  let ⟨contextShape⟩ ← variableShape program x.contextNode x.contextBinder
  let ⟨storageShape⟩ ← allocateShape program x.storageNode x.storageContextNode x.requestNode
  let ⟨storageContextShape⟩ ← variableShape program x.storageContextNode x.contextBinder
  let ⟨requestShape⟩ ← requestShape program x.requestNode (fields.length + constructor.toList.length)
  pure {
    contextBinder := x.contextBinder
    queryNode := x.queryNode
    unitNode := x.unitNode
    tupleNode := x.tupleNode
    contextNode := x.contextNode
    storageNode := x.storageNode
    storageContextNode := x.storageContextNode
    requestNode := x.requestNode
    rootShape := rootShape
    queryShape := queryShape
    unitShape := unitShape
    tupleShape := tupleShape
    contextShape := contextShape
    storageShape := storageShape
    storageContextShape := storageContextShape
    requestShape := requestShape
  }

def checkClosure (program : Program) (x : ClosureCoordinates) : Option (CheckedClosure program x.root) := do
  let ⟨rootShape⟩ ← bindShape program x.root x.contextBinder x.queryNode x.closureNode
  let ⟨queryShape⟩ ← queryShape program x.queryNode x.unitNode
  let ⟨unitShape⟩ ← unitShape program x.unitNode
  let ⟨closureShape⟩ ← closureShape program x.closureNode x.contextNode [] x.storageNode x.parameter x.body
  let ⟨contextShape⟩ ← variableShape program x.contextNode x.contextBinder
  let ⟨storageShape⟩ ← allocateShape program x.storageNode x.storageContextNode x.requestNode
  let ⟨storageContextShape⟩ ← variableShape program x.storageContextNode x.contextBinder
  let ⟨requestShape⟩ ← requestShape program x.requestNode 1
  pure {
    contextBinder := x.contextBinder
    queryNode := x.queryNode
    unitNode := x.unitNode
    closureNode := x.closureNode
    contextNode := x.contextNode
    storageNode := x.storageNode
    storageContextNode := x.storageContextNode
    requestNode := x.requestNode
    parameter := x.parameter
    body := x.body
    rootShape := rootShape
    queryShape := queryShape
    unitShape := unitShape
    closureShape := closureShape
    contextShape := contextShape
    storageShape := storageShape
    storageContextShape := storageContextShape
    requestShape := requestShape
  }

structure InsertCoordinates where
  code : NodeId
  context : NodeId
  storage : NodeId
  captureNodes : List NodeId
  parameter : Binder
  body : NodeId
  argumentScrutinee : NodeId
  listBody : NodeId
  listScrutinee : NodeId
  emptyBody : NodeId
  moreBody : NodeId
  singletonEntry : NodeId
  singletonEmpty : NodeId
  prependEntry : NodeId
  recursiveCall : NodeId
  recursiveFunction : NodeId
  recursiveEntry : NodeId
  recursiveTail : NodeId
  singletonOperand : NodeId
  prependOperand : NodeId
  newName : Binder
  listName : Binder
  entryName : Binder
  tailName : Binder
  functionName : Binder
  singletonClosure : ClosureCoordinates
  singletonPair : TupleCoordinates
  singletonValue : TupleCoordinates
  emptyValue : TupleCoordinates
  prependClosure : ClosureCoordinates
  prependPair : TupleCoordinates
  prependValue : TupleCoordinates
  recursivePair : TupleCoordinates

/-- Decode each required actual graph edge; exhaustion or mismatch yields no judgment. -/
def checkInsert (c : Constructors) (program : Program) (x : InsertCoordinates) : Option (CheckedInsert c program) := do
  let singletonClosure ← checkClosure program x.singletonClosure
  let singletonPair ← checkTuple program x.singletonPair none [x.singletonEntry, x.singletonEmpty]
  let singletonValue ← checkTuple program { x.singletonValue with root := singletonClosure.body } (some c.more) [x.singletonOperand]
  let emptyValue ← checkTuple program { x.emptyValue with root := x.singletonEmpty } (some c.empty) []
  let prependClosure ← checkClosure program x.prependClosure
  let prependPair ← checkTuple program x.prependPair none [x.prependEntry, x.recursiveCall]
  let prependValue ← checkTuple program { x.prependValue with root := prependClosure.body } (some c.more) [x.prependOperand]
  let recursivePair ← checkTuple program x.recursivePair none [x.recursiveEntry, x.recursiveTail]
  if x.emptyValue.root = x.singletonEmpty then
  if singletonClosure.body = x.singletonValue.root then
  if prependClosure.body = x.prependValue.root then
  let ⟨closureShape⟩ ← closureShape program x.code x.context x.captureNodes x.storage x.parameter x.body
  let ⟨bodyShape⟩ ← argumentMatchShape program x.body x.argumentScrutinee x.newName x.listName x.listBody
  let ⟨argumentShape⟩ ← variableShape program x.argumentScrutinee x.parameter
  let ⟨listShape⟩ ← listMatchShape program x.listBody x.listScrutinee c.empty c.more x.entryName x.tailName x.emptyBody x.moreBody
  let ⟨listVariableShape⟩ ← variableShape program x.listScrutinee x.listName
  let ⟨singletonShape⟩ ← applyShape program x.emptyBody x.singletonClosure.root x.singletonPair.root
  let ⟨singletonEntryShape⟩ ← variableShape program x.singletonEntry x.newName
  let ⟨singletonOperandShape⟩ ← variableShape program x.singletonOperand singletonClosure.parameter
  let ⟨prependShape⟩ ← applyShape program x.moreBody x.prependClosure.root x.prependPair.root
  let ⟨prependEntryShape⟩ ← variableShape program x.prependEntry x.entryName
  let ⟨prependOperandShape⟩ ← variableShape program x.prependOperand prependClosure.parameter
  let ⟨recursiveShape⟩ ← applyShape program x.recursiveCall x.recursiveFunction x.recursivePair.root
  let ⟨recursiveFunctionShape⟩ ← variableShape program x.recursiveFunction x.functionName
  let ⟨recursiveEntryShape⟩ ← variableShape program x.recursiveEntry x.newName
  let ⟨recursiveTailShape⟩ ← variableShape program x.recursiveTail x.tailName
  if h15 : x.newName ≠ singletonPair.contextBinder then
  if h16 : singletonClosure.parameter ≠ singletonValue.contextBinder then
  if h17 : x.entryName ≠ prependPair.contextBinder then
  if h18 : x.functionName ≠ prependPair.contextBinder then
  if h19 : x.newName ≠ prependPair.contextBinder then
  if h20 : x.tailName ≠ prependPair.contextBinder then
  if h21 : prependClosure.parameter ≠ prependValue.contextBinder then
  if h22 : x.newName ≠ recursivePair.contextBinder then
  if h23 : x.tailName ≠ recursivePair.contextBinder then
  if h24 : [x.parameter, x.newName, x.listName, x.entryName, x.tailName, x.functionName].Nodup then
  some {
      code := x.code
      context := x.context
      storage := x.storage
      captureNodes := x.captureNodes
      parameter := x.parameter
      body := x.body
      argumentScrutinee := x.argumentScrutinee
      listBody := x.listBody
      listScrutinee := x.listScrutinee
      emptyBody := x.emptyBody
      moreBody := x.moreBody
      singletonEntry := x.singletonEntry
      singletonEmpty := x.singletonEmpty
      prependEntry := x.prependEntry
      recursiveCall := x.recursiveCall
      recursiveFunction := x.recursiveFunction
      recursiveEntry := x.recursiveEntry
      recursiveTail := x.recursiveTail
      singletonOperand := x.singletonOperand
      prependOperand := x.prependOperand
      newName := x.newName
      listName := x.listName
      entryName := x.entryName
      tailName := x.tailName
      functionName := x.functionName
      singletonFunction := x.singletonClosure.root
      singletonArgument := x.singletonPair.root
      prependFunction := x.prependClosure.root
      prependArgument := x.prependPair.root
      recursiveArgument := x.recursivePair.root
      singletonClosure := singletonClosure
      singletonPair := singletonPair
      singletonValue := singletonValue
      emptyValue := emptyValue
      prependClosure := prependClosure
      prependPair := prependPair
      prependValue := prependValue
      recursivePair := recursivePair
      closureShape := closureShape
      bodyShape := bodyShape
      argumentShape := argumentShape
      listShape := listShape
      listVariableShape := listVariableShape
      singletonShape := singletonShape
      singletonEntryShape := singletonEntryShape
      singletonOperandShape := singletonOperandShape
      prependShape := prependShape
      prependEntryShape := prependEntryShape
      prependOperandShape := prependOperandShape
      recursiveShape := recursiveShape
      recursiveFunctionShape := recursiveFunctionShape
      recursiveEntryShape := recursiveEntryShape
      recursiveTailShape := recursiveTailShape
      singletonEntryFresh := h15
      singletonOperandFresh := h16
      prependEntryFresh := h17
      recursiveFunctionFresh := h18
      recursiveEntryInPrependFresh := h19
      recursiveTailInPrependFresh := h20
      prependOperandFresh := h21
      recursiveEntryFresh := h22
      recursiveTailFresh := h23
      distinct := h24
  }
  else none
  else none
  else none
  else none
  else none
  else none
  else none
  else none
  else none
  else none
  else none
  else none
  else none


/-- Every judgment returned by the executable decoder has the proved insertion behavior. -/
theorem accepted_insert_normal_return (c : Constructors) (program : Program) (x : InsertCoordinates)
    (checked : CheckedInsert c program) (accepted : checkInsert c program x = some checked)
    (captureValues : List Value) (captureEnv : Environment) (selfAddress selfResolved : Nat)
    (newEntry : Value) (newAddress : Nat) (newLocation : newEntry = .location newAddress)
    (key : Value → Id) (entries : List Value)
    (selfBinding : CoreEval.lookup captureEnv.reverse checked.functionName = some (.location selfAddress))
    (captureBindings : CaptureBindings program checked.captureNodes captureValues captureEnv) :
    ∀ start finish payload payloadResolved list result,
      Resolve start payload payloadResolved → readCell start payloadResolved = some [newEntry, list] →
      BoundedLocations start → Children c start list entries → KeyedEntries c start key entries →
      Resolve start selfAddress selfResolved →
      readCell start selfResolved = some (.closureCode checked.code :: captureValues) →
      Eval program (extend captureEnv.reverse checked.parameter (.location payload)) checked.body start result finish →
      InsertOutcome c start finish result (entries ++ [newEntry]) := by
  cases actual : checkInsert c program x with
  | none => simp [actual] at accepted
  | some decoded =>
    have same : decoded = checked := Option.some.inj (actual.symm.trans accepted)
    subst checked
    exact insertion_body_correct c program decoded captureValues captureEnv selfAddress selfResolved
      newEntry newAddress newLocation key entries selfBinding captureBindings

end Ash.NetworkLedger.CoreInsertBinding
