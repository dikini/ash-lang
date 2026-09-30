import ScopedExecution

/-! Distinct finite Core syntax for the bounded TASK-0032 comparison.
Postorder indices address this graph; original arena IDs are retained data, not
proof that Rust exported them correctly. Types, rows, binders and source spans
are retained for a later static certificate compiler. This checker establishes
representation shape and fragment membership, not Core typing or admission. -/
namespace Ash.OneShot.CoreSyntax
open Instantiation

abbrev NodeRef := Nat

inductive UnsupportedType where
  | nominal | variable | inference
  deriving DecidableEq, Repr

/-- Structural Core types, not calculus callable ports. Capture support is not
    inferred from these types. -/
inductive ValueType where
  | unit | boolean | integer
  | product : ValueType → ValueType → ValueType
  | reference : ResourceName → ValueType
  | function : ValueType → ValueType → List Effect → ValueType
  | unsupported : UnsupportedType → ValueType
  deriving DecidableEq, Repr

def ValueType.supported : ValueType → Bool
  | .unit | .boolean | .integer | .reference _ => true
  | .product left right | .function left right _ => left.supported && right.supported
  | .unsupported _ => false

structure Binder where
  id : Nat
  type : ValueType
  deriving DecidableEq, Repr

structure SourceSpan where
  moduleId : Nat
  sourceId : Nat
  start : Nat
  stop : Nat
  deriving DecidableEq, Repr

/-- Raw patterns remain visible until translation checks their exact form. -/
inductive Pattern where
  | unit
  | boolean : Bool → Pattern
  | binder : Binder → Pattern
  | unsupported : Nat → Pattern
  deriving DecidableEq, Repr

structure MatchArm where
  pattern : Pattern
  body : NodeRef
  deriving DecidableEq, Repr

structure Clause where
  operation : Nat
  argument : Pattern
  owner : Nat
  body : NodeRef
  deriving DecidableEq, Repr

structure GlobalMember where
  binder : Binder
  initializer : NodeRef
  deriving DecidableEq, Repr

inductive UnsupportedNode where
  | constructor | primitive | newtypeConversion | localNominalScope
  | typeAbstraction | typeApplication | registration
  deriving DecidableEq, Repr

/-- Static use-state outcome stored by Core; this is not runtime liveness. -/
inductive ResumeUse where
  | available | consumed
  deriving DecidableEq, Repr

inductive Kind where
  | unit
  | boolean : Bool → Kind
  | integer : Int → Kind
  | variable : Nat → Kind
  | function : Binder → NodeRef → Kind
  | apply : NodeRef → NodeRef → Kind
  | bind : Binder → NodeRef → NodeRef → Kind
  | tuple : List NodeRef → Kind
  | matchCases : NodeRef → List MatchArm → Kind
  | request : Effect → Nat → NodeRef → Kind
  | handler : Nat → Effect → NodeRef → List Clause → Kind
  | resume : Nat → Nat → ResumeUse → NodeRef → Kind
  | discard : Nat → Nat → ResumeUse → Kind
  | resource : Nat → Binder → NodeRef → NodeRef → Kind
  | cleanup : Binder → NodeRef → NodeRef → Kind
  | recursiveBind : List GlobalMember → NodeRef → Kind
  | unsupported : UnsupportedNode → Kind
  deriving DecidableEq, Repr

def Kind.children : Kind → List NodeRef
  | .unit | .boolean _ | .integer _ | .variable _ | .discard _ _ _ | .unsupported _ => []
  | .function _ body | .request _ _ body | .resume _ _ _ body => [body]
  | .apply left right | .bind _ left right | .resource _ _ left right => [left, right]
  | .tuple elements => elements
  | .matchCases scrutinee arms => scrutinee :: arms.map (·.body)
  | .handler _ _ body clauses => body :: clauses.map (·.body)
  | .cleanup _ action body => [action, body]
  | .recursiveBind members body => members.map (·.initializer) ++ [body]

/-- Names reserve space before administrative binders are chosen. -/
def Kind.names : Kind → List Nat
  | .variable name => [name]
  | .function binder _ | .bind binder _ _ | .cleanup binder _ _ => [binder.id]
  | .resource identity binder _ _ => [identity, binder.id]
  | .matchCases _ arms => arms.flatMap fun arm => match arm.pattern with
      | .binder binder => [binder.id]
      | _ => []
  | .handler _ _ _ clauses => clauses.flatMap fun clause => match clause.argument with
      | .binder binder => [binder.id]
      | _ => []
  | .recursiveBind members _ => members.map (·.binder.id)
  | _ => []

def Kind.binders : Kind → List Binder
  | .function binder _ | .bind binder _ _ | .cleanup binder _ _ | .resource _ binder _ _ => [binder]
  | .handler _ _ _ clauses => clauses.filterMap fun clause => match clause.argument with
      | .binder binder => some binder
      | _ => none
  | .matchCases _ arms => arms.filterMap fun arm => match arm.pattern with
      | .binder binder => some binder
      | _ => none
  | .recursiveBind members _ => members.map (·.binder)
  | _ => []

structure Node where
  originalId : Nat
  type : ValueType
  effects : List Effect
  source : Option SourceSpan
  kind : Kind
  deriving DecidableEq, Repr

structure Graph where
  nodes : List Node
  root : NodeRef
  deriving DecidableEq, Repr

def Graph.node (graph : Graph) (reference : NodeRef) : Option Node := graph.nodes[reference]?

def Graph.freshBase (graph : Graph) : Nat :=
  1 + (graph.nodes.flatMap fun node => node.kind.names).foldl max 0

private theorem initial_le_foldMax (names : List Nat) (initial : Nat) :
    initial ≤ names.foldl max initial := by
  induction names generalizing initial with
  | nil => exact Nat.le_refl initial
  | cons head tail ih =>
      exact Nat.le_trans (Nat.le_max_left initial head) (ih (max initial head))

private theorem member_le_foldMax (names : List Nat) (name initial : Nat)
    (member : name ∈ names) : name ≤ names.foldl max initial := by
  induction names generalizing initial with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with same | member
      · subst name
        exact Nat.le_trans (Nat.le_max_right initial head) (initial_le_foldMax tail (max initial head))
      · exact ih (max initial head) member

theorem Graph.name_lt_freshBase (graph : Graph) (name : Nat)
    (member : name ∈ graph.nodes.flatMap (fun node => node.kind.names)) :
    name < graph.freshBase := by
  have bound := member_le_foldMax (graph.nodes.flatMap fun node => node.kind.names) name 0 member
  simpa [Graph.freshBase, Nat.add_comm] using Nat.lt_succ_of_le bound

inductive Error where
  | invalidRoot : NodeRef → Error
  | missingNode : NodeRef → Error
  | duplicateOriginalId : Nat → Error
  | childOrder : NodeRef → NodeRef → Error
  | unsupportedNode : NodeRef → UnsupportedNode → Error
  | unsupportedType : NodeRef → Error
  | unsupportedTuple : NodeRef → Nat → Error
  | unsupportedMatch : NodeRef → Error
  | unsupportedClausePattern : NodeRef → Nat → Error
  | duplicateOperation : NodeRef → Nat → Error
  | duplicateOwner : NodeRef → Nat → Error
  | ownerNotActive : NodeRef → Nat → Nat → Error
  | ownerHandlerMismatch : NodeRef → Nat → Nat → Error
  | cleanupActionShape : NodeRef → NodeRef → Error
  | recursiveGroup : NodeRef → Nat → Error
  | recursiveInitializer : NodeRef → Nat → Error
  | unconsumedUse : NodeRef → Error
  | fuelExhausted : NodeRef → Error
  deriving DecidableEq, Repr

/-- Local fragment checks apply even to unreachable arena slots. Clause
    coverage against declarations remains a metadata/admission obligation. -/
def checkClauseShapes (index : NodeRef) (clauses : List Clause) : Except Error Unit := do
  let mut operations : List Nat := []
  let mut owners : List Nat := []
  for clause in clauses do
    if operations.contains clause.operation then throw (.duplicateOperation index clause.operation)
    if owners.contains clause.owner then throw (.duplicateOwner index clause.owner)
    operations := clause.operation :: operations
    owners := clause.owner :: owners
    match clause.argument with
    | .binder _ => pure ()
    | _ => throw (.unsupportedClausePattern index clause.operation)
  pure ()

def checkFragment (index : NodeRef) : Kind → Except Error Unit
  | .unsupported kind => .error (.unsupportedNode index kind)
  | .tuple [_, _] => .ok ()
  | .tuple elements => .error (.unsupportedTuple index elements.length)
  | .matchCases _ [⟨.unit, _⟩] => .ok ()
  | .matchCases _ [⟨.boolean true, _⟩, ⟨.boolean false, _⟩]
    | .matchCases _ [⟨.boolean false, _⟩, ⟨.boolean true, _⟩] => .ok ()
  | .matchCases _ _ => .error (.unsupportedMatch index)
  | .handler _ _ _ clauses => checkClauseShapes index clauses
  | .resume _ _ .available _ | .discard _ _ .available => .error (.unconsumedUse index)
  | .recursiveBind [_] _ => .ok ()
  | .recursiveBind members _ => .error (.recursiveGroup index members.length)
  | _ => .ok ()

/-- Strictly earlier child slots exclude cycles and missing references. All
    slots are checked, including nodes unreachable from the root. -/
def checkShape (graph : Graph) : Except Error Unit := do
  if graph.root >= graph.nodes.length then throw (.invalidRoot graph.root)
  let mut originals : List Nat := []
  for (node, index) in graph.nodes.zipIdx do
    if originals.contains node.originalId then throw (.duplicateOriginalId node.originalId)
    originals := node.originalId :: originals
    if !node.type.supported || !(node.kind.binders.all fun binder => binder.type.supported) then
      throw (.unsupportedType index)
    checkFragment index node.kind
    for child in node.kind.children do
      if child >= index then throw (.childOrder index child)
  pure ()

/-- Only executable shape truth; no static metadata or admission derivation. -/
def ShapeChecked (graph : Graph) : Prop := checkShape graph = .ok ()

namespace Examples

def unitNode : Node := ⟨17, .unit, [], none, .unit⟩

example : checkShape ⟨[unitNode], 0⟩ = .ok () := rfl
example : checkShape ⟨[], 0⟩ = .error (.invalidRoot 0) := rfl
example : checkShape ⟨[unitNode, unitNode], 1⟩ = .error (.duplicateOriginalId 17) := rfl
example : checkShape ⟨[⟨0, .unit, [], none, .apply 0 0⟩], 0⟩ =
    .error (.childOrder 0 0) := rfl
example : checkShape ⟨[⟨0, .unit, [], none, .unsupported .registration⟩], 0⟩ =
    .error (.unsupportedNode 0 .registration) := rfl

end Examples
end Ash.OneShot.CoreSyntax

#print axioms Ash.OneShot.CoreSyntax.Graph.name_lt_freshBase
