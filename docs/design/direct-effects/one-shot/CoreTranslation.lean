import CoreSyntax

/-! Syntax translation for TASK-0032's finite Core graph. No calculus Program
or admission derivation is an input. This does not validate retained type/row
metadata, Rust exports, closure support or admission. Operands stay nested;
there is no ANF conversion. -/
namespace Ash.OneShot.CoreTranslation
open Instantiation ScopedExpressions CoreSyntax

structure OwnerBinding where
  handler : Nat
  owner : Nat
  ticket : Nat
  deriving DecidableEq, Repr

abbrev OwnerMap := List OwnerBinding

/-- Administrative variables and tickets occupy separate ranges above original
    variable names. Ordinary and ticket dependency namespaces also stay distinct. -/
def dummy (graph : Graph) (index : NodeRef) : Nat := graph.freshBase + index

def ticket (graph : Graph) (owner : Nat) : Nat := graph.freshBase + graph.nodes.length + owner

theorem ticket_injective (graph : Graph) (a b : Nat)
    (same : ticket graph a = ticket graph b) : a = b :=
  Nat.add_left_cancel same

theorem dummy_ne_ticket (graph : Graph) (index owner : Nat)
    (bounded : index < graph.nodes.length) : dummy graph index ≠ ticket graph owner := by
  have bound : index < graph.nodes.length + owner :=
    Nat.lt_of_lt_of_le bounded (Nat.le_add_right graph.nodes.length owner)
  apply Nat.ne_of_lt
  simpa [dummy, ticket, Nat.add_assoc] using Nat.add_lt_add_left bound graph.freshBase

def resolveOwner (owners : OwnerMap) (index handler owner : Nat) : Except Error Nat := do
  match owners.find? (fun binding => binding.owner == owner) with
  | none => throw (.ownerNotActive index handler owner)
  | some binding =>
      if binding.handler != handler then throw (.ownerHandlerMismatch index handler owner)
      pure binding.ticket

def requireNode (graph : Graph) (index : NodeRef) : Except Error Node :=
  match graph.node index with
  | none => .error (.missingNode index)
  | some node => .ok node

/-- Check the actual stored ordinary invocation `callback ()`. -/
def checkCleanup (graph : Graph) (index : NodeRef) (callback : Binder)
    (action : NodeRef) : Except Error Unit := do
  let actionNode ← requireNode graph action
  match actionNode.kind with
  | .apply function argument =>
      let functionNode ← requireNode graph function
      let argumentNode ← requireNode graph argument
      match functionNode.kind, argumentNode.kind with
      | .variable binder, .unit =>
          if binder == callback.id then pure () else throw (.cleanupActionShape index action)
      | _, _ => throw (.cleanupActionShape index action)
  | _ => throw (.cleanupActionShape index action)

/-- Total fuel-bounded recursion; exhaustion is an explicit failure. Strict
    postorder graph checking precedes the public entry point. -/
def translateFuel (graph : Graph) : Nat → OwnerMap → NodeRef → Except Error Code
  | 0, _, index => .error (.fuelExhausted index)
  | fuel + 1, owners, index => do
    let node ← requireNode graph index
    match node.kind with
    | .unit => pure .unit
    | .boolean value => pure (.boolean value)
    | .integer value => pure (.integer value)
    | .variable binder => pure (.variable binder)
    | .function binder body =>
        pure (.lambda binder.id (← translateFuel graph fuel owners body))
    | .apply function argument =>
        pure (.app (← translateFuel graph fuel owners function) (← translateFuel graph fuel owners argument))
    | .bind binder initializer body =>
        pure (.bind binder.id (← translateFuel graph fuel owners initializer) (← translateFuel graph fuel owners body))
    | .tuple [left, right] =>
        pure (.pair (← translateFuel graph fuel owners left) (← translateFuel graph fuel owners right))
    | .tuple elements => throw (.unsupportedTuple index elements.length)
    | .matchCases scrutinee [⟨.unit, body⟩] =>
        pure (.bind (dummy graph index) (← translateFuel graph fuel owners scrutinee) (← translateFuel graph fuel owners body))
    | .matchCases scrutinee [⟨.boolean true, yes⟩, ⟨.boolean false, no⟩]
      | .matchCases scrutinee [⟨.boolean false, no⟩, ⟨.boolean true, yes⟩] =>
        pure (.branch (← translateFuel graph fuel owners scrutinee)
          (← translateFuel graph fuel owners yes) (← translateFuel graph fuel owners no))
    | .matchCases _ _ => throw (.unsupportedMatch index)
    | .request effect operation operand =>
        pure (.perform effect operation (← translateFuel graph fuel owners operand))
    | .handler handler effect body clauses =>
        checkClauseShapes index clauses
        let translatedBody ← translateFuel graph fuel owners body
        let translatedClauses ← clauses.mapM fun clause => do
          if owners.any (fun binding => binding.owner == clause.owner) then
            throw (.duplicateOwner index clause.owner)
          match clause.argument with
          | .binder argument =>
              let mapped := ticket graph clause.owner
              let clauseOwners := ⟨handler, clause.owner, mapped⟩ :: owners
              let translated ← translateFuel graph fuel clauseOwners clause.body
              pure (clause.operation, argument.id, mapped, translated)
          | _ => throw (.unsupportedClausePattern index clause.operation)
        let table := translatedClauses.foldr
          (fun (operation, argument, mapped, translated) rest =>
            Clauses.cons operation argument mapped translated rest) Clauses.nil
        pure (.handle effect translatedBody table)
    | .resume handler owner _ operand =>
        let mapped ← resolveOwner owners index handler owner
        pure (.resume mapped (← translateFuel graph fuel owners operand))
    | .discard handler owner _ => pure (.discard (← resolveOwner owners index handler owner))
    | .resource identity handle initializer body =>
        pure (.resource identity (← translateFuel graph fuel owners initializer)
          (.bind handle.id (.resourceRef (.bound identity)) (← translateFuel graph fuel owners body)))
    | .cleanup callback action body =>
        checkCleanup graph index callback action
        pure (.cleanup (.variable callback.id) (← translateFuel graph fuel owners body))
    | .recursiveBind [member] body =>
        let initializer ← translateFuel graph fuel owners member.initializer
        if initializer.dependencies.contains (.variable member.binder.id) then
          throw (.recursiveInitializer index member.binder.id)
        pure (.bind member.binder.id initializer (← translateFuel graph fuel owners body))
    | .recursiveBind members _ => throw (.recursiveGroup index members.length)
    | .unsupported kind => throw (.unsupportedNode index kind)

/-- Syntax translation only. Type/row, export and admission checking are open. -/
def translate (graph : Graph) : Except Error Code := do
  checkShape graph
  translateFuel graph (graph.nodes.length + 1) [] graph.root

@[simp] theorem zero_fuel (graph : Graph) (owners : OwnerMap) (index : NodeRef) :
    translateFuel graph 0 owners index = .error (.fuelExhausted index) := rfl

/-- Exact effect identities and the strict nested operand remain unchanged. -/
theorem request_equation (graph : Graph) (owners : OwnerMap) (fuel index : Nat)
    (node : Node) (effect : Effect) (operation operand : Nat)
    (known : graph.node index = some node) (kind : node.kind = .request effect operation operand) :
    translateFuel graph (fuel + 1) owners index = (do
      pure (.perform effect operation (← translateFuel graph fuel owners operand))) := by
  cases node with
  | mk original type effects source nodeKind =>
      cases kind
      simp only [translateFuel, requireNode, known]
      rfl

/-- The initializer stays outside the resource's handle binding. -/
theorem resource_equation (graph : Graph) (owners : OwnerMap) (fuel index : Nat)
    (node : Node) (identity : Nat) (handle : Binder) (initializer body : Nat)
    (known : graph.node index = some node)
    (kind : node.kind = .resource identity handle initializer body) :
    translateFuel graph (fuel + 1) owners index = (do
      pure (.resource identity (← translateFuel graph fuel owners initializer)
        (.bind handle.id (.resourceRef (.bound identity)) (← translateFuel graph fuel owners body)))) := by
  cases node with
  | mk original type effects source nodeKind =>
      cases kind
      simp only [translateFuel, requireNode, known]
      rfl

/-- A checked shape supplies the public entry's bounded graph traversal,
    without supplying any calculus typing or source-admission proof. -/
theorem translate_of_shape (graph : Graph) (checked : ShapeChecked graph) :
    translate graph = translateFuel graph (graph.nodes.length + 1) [] graph.root := by
  unfold translate
  rw [checked]
  rfl

/-- Cleanup translates its actual checked callback invocation to the callback
    value expected by Code.cleanup; it does not evaluate the stored action now. -/
theorem cleanup_equation (graph : Graph) (owners : OwnerMap) (fuel index : Nat)
    (node : Node) (callback : Binder) (action body : Nat)
    (known : graph.node index = some node) (kind : node.kind = .cleanup callback action body)
    (authenticated : checkCleanup graph index callback action = .ok ()) :
    translateFuel graph (fuel + 1) owners index = (do
      pure (.cleanup (.variable callback.id) (← translateFuel graph fuel owners body))) := by
  cases node with
  | mk original type effects source nodeKind =>
      cases kind
      simp only [translateFuel, requireNode, known]
      change (do
        checkCleanup graph index callback action
        pure (Code.cleanup (Code.variable callback.id) (← translateFuel graph fuel owners body))) = _
      rw [authenticated]
      rfl

namespace Examples

def node (original : Nat) (kind : CoreSyntax.Kind) (type : CoreSyntax.ValueType := .unit)
    (effects : List Effect := []) : Node := ⟨original, type, effects, none, kind⟩

def exact : Effect := .user 91 [.resource (.bound 3), .nominal 27]

def strictRequest : Graph := ⟨[
  node 9 .unit, node 15 (.request (.user 92 []) 0 0), node 21 (.request exact 4 1)], 2⟩

example : translate strictRequest = .ok (.perform exact 4 (.perform (.user 92 []) 0 .unit)) := rfl
example : translate ⟨[node 0 (.tuple [])], 0⟩ = .error (.unsupportedTuple 0 0) := rfl
example : translate ⟨[node 0 (.discard 1 2 .consumed)], 0⟩ = .error (.ownerNotActive 0 1 2) := rfl
example : resolveOwner [⟨1, 2, 7⟩] 0 8 2 = .error (.ownerHandlerMismatch 0 8 2) := rfl
example : translate ⟨[node 0 .unit, node 1 (.matchCases 0 [⟨.boolean true, 0⟩])], 1⟩ =
    .error (.unsupportedMatch 1) := rfl
example : translate ⟨[node 0 .unit, node 1 (.cleanup ⟨4, .function .unit .unit []⟩ 0 0)], 1⟩ =
    .error (.cleanupActionShape 1 0) := rfl
example : translate ⟨[node 0 .unit, node 1 (.recursiveBind [] 0)], 1⟩ =
    .error (.recursiveGroup 1 0) := rfl
example : translate ⟨[node 0 (.variable 4),
    node 1 (.recursiveBind [⟨⟨4, .unit⟩, 0⟩] 0)], 1⟩ =
    .error (.recursiveInitializer 1 4) := rfl


def ownedHandler : Graph := ⟨[
  node 0 .unit,
  node 1 (.request exact 0 0),
  node 2 (.resume 7 4 .consumed 0),
  node 3 (.handler 7 exact 1 [⟨0, .binder ⟨2, .unit⟩, 4, 2⟩])], 3⟩

example : translate ownedHandler = .ok (.handle exact (.perform exact 0 .unit)
    (.cons 0 2 11 (.resume 11 .unit) .nil)) := rfl

example : checkClauseShapes 5 [⟨0, .unit, 4, 0⟩] =
    .error (.unsupportedClausePattern 5 0) := rfl
example : checkClauseShapes 5 [⟨0, .binder ⟨2, .unit⟩, 4, 0⟩,
    ⟨0, .binder ⟨3, .unit⟩, 5, 0⟩] = .error (.duplicateOperation 5 0) := rfl
example : checkClauseShapes 5 [⟨0, .binder ⟨2, .unit⟩, 4, 0⟩,
    ⟨1, .binder ⟨3, .unit⟩, 4, 0⟩] = .error (.duplicateOwner 5 4) := rfl

def authenticatedCleanup : Graph := ⟨[
  node 0 .unit,
  node 1 (.function ⟨8, .unit⟩ 0) (.function .unit .unit []),
  node 2 (.variable 5) (.function .unit .unit []),
  node 3 (.apply 2 0),
  node 4 (.cleanup ⟨5, .function .unit .unit []⟩ 3 0),
  node 5 (.bind ⟨5, .function .unit .unit []⟩ 1 4)], 5⟩

example : translate authenticatedCleanup =
    .ok (.bind 5 (.lambda 8 .unit) (.cleanup (.variable 5) .unit)) := rfl

/-- Wrong callback identity cannot authenticate the stored invocation. -/
example : checkCleanup authenticatedCleanup 4 ⟨6, .function .unit .unit []⟩ 3 =
    .error (.cleanupActionShape 4 3) := rfl

example : translate ⟨[
    node 0 (.integer 0) .integer,
    node 1 (.variable 4) (.reference (.bound 3)),
    node 2 (.resource 3 ⟨4, .reference (.bound 3)⟩ 0 1) (.reference (.bound 3))], 2⟩ =
    .ok (.resource 3 (.integer 0) (.bind 4 (.resourceRef (.bound 3)) (.variable 4))) := rfl

/-- The strict effectful Unit scrutinee is retained before the arm body. -/
example : translate ⟨[node 0 .unit, node 1 (.request exact 0 0),
    node 2 (.integer 17) .integer,
    node 3 (.matchCases 1 [⟨.unit, 2⟩]) .integer], 3⟩ =
    .ok (.bind 4 (.perform exact 0 .unit) (.integer 17)) := rfl

/-- Both exhaustive Boolean arm orders give the same branch nesting. -/
example : translate ⟨[node 0 (.boolean true) .boolean,
    node 1 (.integer 11) .integer, node 2 (.integer 7) .integer,
    node 3 (.matchCases 0 [⟨.boolean false, 2⟩, ⟨.boolean true, 1⟩]) .integer], 3⟩ =
    .ok (.branch (.boolean true) (.integer 11) (.integer 7)) := rfl

example : translate ⟨[node 0 .unit,
    node 1 (.function ⟨8, .unit⟩ 0) (.function .unit .unit []),
    node 2 (.variable 5) (.function .unit .unit []),
    node 3 (.recursiveBind [⟨⟨5, .function .unit .unit []⟩, 1⟩] 2) (.function .unit .unit [])], 3⟩ =
    .ok (.bind 5 (.lambda 8 .unit) (.variable 5)) := rfl

/-- Only the validator's stored consumed outcome belongs to this fragment. -/
example : translate ⟨[node 0 (.discard 1 2 .available)], 0⟩ =
    .error (.unconsumedUse 0) := rfl

example : requireNode ⟨[], 0⟩ 9 = .error (.missingNode 9) := rfl
example : translateFuel ownedHandler 5 [⟨8, 4, 99⟩] 3 =
    .error (.duplicateOwner 3 4) := rfl

example : translate ⟨[node 0 .unit, node 1 (.boolean true) .boolean,
    node 2 (.tuple [0, 1]) (.product .unit .boolean)], 2⟩ =
    .ok (.pair .unit (.boolean true)) := rfl

example : translate ⟨[node 0 (.integer 17) .integer, node 1 (.variable 2) .integer,
    node 2 (.function ⟨2, .integer⟩ 1) (.function .integer .integer []),
    node 3 (.apply 2 0) .integer], 3⟩ =
    .ok (.app (.lambda 2 (.variable 2)) (.integer 17)) := rfl

example : translate ⟨[node 0 .unit, node 1 (.request exact 0 0),
    node 2 (.discard 7 4 .consumed),
    node 3 (.handler 7 exact 1 [⟨0, .binder ⟨2, .unit⟩, 4, 2⟩])], 3⟩ =
    .ok (.handle exact (.perform exact 0 .unit) (.cons 0 2 11 (.discard 11) .nil)) := rfl

end Examples
end Ash.OneShot.CoreTranslation

#print axioms Ash.OneShot.CoreTranslation.request_equation
#print axioms Ash.OneShot.CoreTranslation.resource_equation
#print axioms Ash.OneShot.CoreTranslation.cleanup_equation
#print axioms Ash.OneShot.CoreTranslation.translate_of_shape
#print axioms Ash.OneShot.CoreTranslation.ticket_injective
#print axioms Ash.OneShot.CoreTranslation.dummy_ne_ticket
