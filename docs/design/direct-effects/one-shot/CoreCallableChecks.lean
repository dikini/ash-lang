import CoreTranslation
import CoreTranslationFuel
import CoreExportedFixture
import CoreValueRelation
import CoreAdministrativeSteps

/-! Executable static certificates for identified function sites in retained
Core graph data. Shape checking, empty-owner translation and absence of free
lambda tickets are checked directly, without runtime or Program premises.

The current Rust validator rejects free continuations at function barriers,
but a general authentication theorem connecting its scope analysis to these
graph checks is still separate. Nested callable sites need their own checks. -/
namespace Ash.OneShot.CoreCallableChecks
open ScopedExpressions CoreSyntax CoreTranslation

inductive Error where
  | shape : CoreSyntax.Error → Error
  | missingSite : Nat → Error
  | notFunction : Nat → Error
  | translation : CoreSyntax.Error → Error
  | outerTicket
  | ambientMismatch
  deriving DecidableEq, Repr

structure CheckedCallable where
  parameter : Nat
  body : Nat
  rawBody : Code
  deriving Repr

def isTicket : Syntax.Dependency → Bool
  | .ticket _ => true
  | _ => false

def noOuterTicket (parameter : Nat) (body : Code) : Bool :=
  !((Code.lambda parameter body).dependencies.any isTicket)

/-- Check the whole graph's existing shape obligations, then obtain this exact
site independently of graph.root. Empty OwnerMap is the callable barrier. -/
def checkFunction (graph : Graph) (site : NodeRef) : Except Error CheckedCallable := do
  (checkShape graph).mapError Error.shape
  let node ← match graph.node site with
    | none => .error (.missingSite site)
    | some node => .ok node
  match node.kind with
  | .function binder body =>
      let rawBody ← (translateFuel graph (graph.nodes.length + 1) [] body).mapError Error.translation
      if noOuterTicket binder.id rawBody then pure ⟨binder.id, body, rawBody⟩
      else .error .outerTicket
  | _ => .error (.notFunction site)

private theorem bind_ok {α β : Type} (a : Except Error α)
    (f : α → Except Error β) (value : β) (success : a.bind f = .ok value) :
    ∃ item, a = .ok item ∧ f item = .ok value := by
  cases h : a with
  | error e => simp [h, Except.bind] at success
  | ok item => exact ⟨item, rfl, by simpa [h, Except.bind] using success⟩

private theorem mapError_ok {α ε : Type} (a : Except ε α) (f : ε → Error) (value : α)
    (success : a.mapError f = .ok value) : a = .ok value := by
  cases a with
  | error e => simp [Except.mapError] at success
  | ok item => simpa [Except.mapError] using success

theorem noOuterTicket_sound (checked : noOuterTicket parameter body = true) :
    ∀ ticket, Syntax.Dependency.ticket ticket ∉ (Code.lambda parameter body).dependencies := by
  intro ticket member
  have present : (Code.lambda parameter body).dependencies.any isTicket = true :=
    List.any_eq_true.mpr ⟨.ticket ticket, member, rfl⟩
  simp [noOuterTicket, present] at checked

/-- These are the exact static fields required by the callable relation. This
leaf does not import the relation module or supply runtime closing evidence. -/
theorem checkFunction_sound (success : checkFunction graph site = .ok checked) :
    ShapeChecked graph ∧
    (∃ binder node, graph.node site = some node ∧ node.kind = .function binder checked.body ∧
      binder.id = checked.parameter) ∧
    translateFuel graph (graph.nodes.length + 1) [] checked.body = .ok checked.rawBody ∧
    (∀ ticket, Syntax.Dependency.ticket ticket ∉ (Code.lambda checked.parameter checked.rawBody).dependencies) := by
  obtain ⟨shapeResult, shape, rest⟩ := bind_ok _ _ _ success
  cases shapeResult
  have shapeChecked := mapError_ok _ _ _ shape
  cases present : graph.node site with
  | none => simp [present, Bind.bind, Except.bind] at rest
  | some node =>
      simp only [present, Bind.bind, Except.bind] at rest
      split at rest
      · rename_i binder body functionKind
        obtain ⟨rawBody, translated, result⟩ := bind_ok _ _ _ rest
        split at result
        · rename_i ticketsChecked
          have same : CheckedCallable.mk binder.id body rawBody = checked := by
            simpa [Pure.pure, Except.pure] using result
          subst checked
          exact ⟨shapeChecked, ⟨binder, node, rfl, functionKind, rfl⟩,
            mapError_ok _ _ _ translated, noOuterTicket_sound ticketsChecked⟩
        · simp at result
      · simp at rest

/-- The identified body's public budget excludes fuel exhaustion. Other
translation failures (such as a foreign continuation) are still explicit. -/
theorem checked_body_fuel_safe (success : checkFunction graph site = .ok checked) :
    ∀ exhausted, translateFuel graph (graph.nodes.length + 1) [] checked.body ≠
      .error (.fuelExhausted exhausted) := by
  have fields := checkFunction_sound success
  obtain ⟨binder, node, present, functionKind, _⟩ := fields.2.1
  have siteBound : site < graph.nodes.length := (List.getElem?_eq_some_iff.mp present).1
  have childBound := CoreTranslationFuel.checkShape_postorder graph fields.1 site node present checked.body
    (by simp [functionKind, Kind.children])
  exact CoreTranslationFuel.checked_budget_fuel_safe graph fields.1 [] checked.body
    (Nat.lt_trans childBound siteBound)

/- Transparent structural comparison includes every Code/Clauses field,
including complete exact effect instances and ticket bindings. -/
mutual
def codeEq : Code → Code → Bool
  | .unit, .unit => true
  | .boolean a, .boolean b => decide (a = b)
  | .integer a, .integer b => decide (a = b)
  | .variable a, .variable b => decide (a = b)
  | .resourceRef a, .resourceRef b => decide (a = b)
  | .pair a b, .pair c d | .app a b, .app c d | .cleanup a b, .cleanup c d =>
      codeEq a c && codeEq b d
  | .lambda a b, .lambda c d | .resume a b, .resume c d =>
      decide (a = c) && codeEq b d
  | .bind a b c, .bind d e f | .resource a b c, .resource d e f =>
      decide (a = d) && (codeEq b e && codeEq c f)
  | .branch a b c, .branch d e f => codeEq a d && (codeEq b e && codeEq c f)
  | .perform effect operation operand, .perform other otherOperation otherOperand =>
      decide (effect = other) && (decide (operation = otherOperation) && codeEq operand otherOperand)
  | .handle effect body clauses, .handle other otherBody otherClauses =>
      decide (effect = other) && (codeEq body otherBody && clausesEq clauses otherClauses)
  | .discard a, .discard b => decide (a = b)
  | _, _ => false
def clausesEq : Clauses → Clauses → Bool
  | .nil, .nil => true
  | .cons operation parameter ticket body rest, .cons other otherParameter otherTicket otherBody otherRest =>
      decide (operation = other) && (decide (parameter = otherParameter) &&
        (decide (ticket = otherTicket) && (codeEq body otherBody && clausesEq rest otherRest)))
  | _, _ => false
end

mutual
theorem codeEq_sound (left right : Code) (equal : codeEq left right = true) : left = right := by
  cases left <;> cases right <;> simp_all [codeEq, Bool.and_eq_true]
  all_goals repeat (first | obtain ⟨rfl, equal⟩ := equal)
  all_goals first
    | (have same := codeEq_sound _ _ equal; simp_all)
    | (obtain ⟨a, b⟩ := equal
       have sameA := codeEq_sound _ _ a
       have sameB := codeEq_sound _ _ b
       simp_all)
    | (obtain ⟨a, b, c⟩ := equal
       have sameA := codeEq_sound _ _ a
       have sameB := codeEq_sound _ _ b
       have sameC := codeEq_sound _ _ c
       simp_all)
    | (obtain ⟨body, clauses⟩ := equal
       have sameBody := codeEq_sound _ _ body
       have sameClauses := clausesEq_sound _ _ clauses
       simp_all)
    | simp_all
theorem clausesEq_sound (left right : Clauses) (equal : clausesEq left right = true) : left = right := by
  cases left <;> cases right <;> simp_all [clausesEq, Bool.and_eq_true]
  obtain ⟨rfl, rfl, rfl, body, rest⟩ := equal
  have sameBody := codeEq_sound _ _ body
  have sameRest := clausesEq_sound _ _ rest
  simp_all
end

mutual
theorem codeEq_refl (code : Code) : codeEq code code = true := by
  cases code <;> simp [codeEq, codeEq_refl, clausesEq_refl]
theorem clausesEq_refl (clauses : Clauses) : clausesEq clauses clauses = true := by
  cases clauses <;> simp [clausesEq, codeEq_refl, clausesEq_refl]
end

theorem codeEq_iff : codeEq left right = true ↔ left = right := by
  constructor
  · exact codeEq_sound _ _
  · intro same; subst right; exact codeEq_refl _

/-- An ambient translation may succeed with identical code or fail from its
own owner-map collision. No arbitrary ambient-map pruning is assumed. -/
def checkAmbient (graph : Graph) (site : NodeRef) (owners : OwnerMap) : Except Error CheckedCallable := do
  let callable ← checkFunction graph site
  let ambient ← (translateFuel graph (graph.nodes.length + 1) owners callable.body).mapError Error.translation
  if codeEq ambient callable.rawBody then pure callable else .error .ambientMismatch

theorem checkAmbient_sound (success : checkAmbient graph site owners = .ok checked) :
    checkFunction graph site = .ok checked ∧
    translateFuel graph (graph.nodes.length + 1) owners checked.body = .ok checked.rawBody := by
  obtain ⟨callable, first, rest⟩ := bind_ok _ _ _ success
  obtain ⟨ambient, second, result⟩ := bind_ok _ _ _ rest
  split at result
  · rename_i equality
    have same : callable = checked := by simpa [Pure.pure, Except.pure] using result
    subst checked
    have rawSame := codeEq_sound _ _ equality
    rw [rawSame] at second
    exact ⟨first, mapError_ok _ _ _ second⟩
  · simp at result

theorem checkAmbient_complete (first : checkFunction graph site = .ok checked)
    (ambient : translateFuel graph (graph.nodes.length + 1) owners checked.body = .ok checked.rawBody) :
    checkAmbient graph site owners = .ok checked := by
  simp [checkAmbient, first, ambient, Except.mapError, Bind.bind, Except.bind, codeEq_refl, Pure.pure, Except.pure]

/-- Successful retained-graph checks construct the actual callable certificate
used by the value/environment relation, not a parallel certificate type. -/
theorem checkFunction_certificate (success : checkFunction graph site = .ok checked) :
    CoreValueRelation.CallableCertificate graph checked.parameter checked.body checked.rawBody := by
  have fields := checkFunction_sound success
  obtain ⟨binder, node, present, kind, parameter⟩ := fields.2.1
  exact ⟨⟨site, binder, node, present, kind, parameter⟩,
    ⟨graph.nodes.length + 1, fields.2.2.1⟩, fields.2.2.2⟩

theorem checkAmbient_certificate (success : checkAmbient graph site owners = .ok checked) :
    CoreValueRelation.CallableCertificate graph checked.parameter checked.body checked.rawBody ∧
    translateFuel graph (graph.nodes.length + 1) owners checked.body = .ok checked.rawBody := by
  have ambient := checkAmbient_sound success
  exact ⟨checkFunction_certificate ambient.1, ambient.2⟩

/-- Lambda entry consumes the executable check's exact certificate. Environment
closing and closedness remain explicit existing relation premises; the static
checker does not infer either fact from retained metadata. -/
theorem checked_lambda_evaluate {base : CoreMachine.State}
    (success : checkAmbient graph site owners = .ok checked)
    (environment : CoreValueRelation.EnvCloses graph owners base.heap saved
      (.lambda checked.parameter checked.rawBody) target)
    (closed : ClosedValue target) (tail : List CoreMachine.Frame) :
    CoreAdministrativeSteps.ValueWitness graph owners
      { base with control := .evaluate site saved, frames := tail }
      { base with control := .returned (.closure checked.parameter checked.body saved), frames := tail, observations := base.observations ++ [.entered site] } target ∧
    translateFuel graph (graph.nodes.length + 1 + 1) owners site =
      .ok (.lambda checked.parameter checked.rawBody) := by
  have ambient := checkAmbient_sound success
  have fields := checkFunction_sound ambient.1
  obtain ⟨binder, node, present, kind, parameter⟩ := fields.2.1
  have certificate := checkFunction_certificate ambient.1
  have result := CoreAdministrativeSteps.lambda_evaluate (base := base) present kind ambient.2
    (by simpa [parameter] using certificate) (by simpa [parameter] using environment) closed tail
  simpa [parameter] using result

namespace Examples
open CoreTranslation.Examples

/-- This is the actual exported read helper site, using the retained graph
rather than a replacement graph or expected-code execution. -/
example : checkFunction CoreExportedFixture.graph 4 =
    .ok ⟨1, 3, .perform (.cell (.bound 0)) 0 (.variable 1)⟩ := rfl

example : checkAmbient CoreExportedFixture.graph 4 [⟨999, 999, 42⟩] =
    .ok ⟨1, 3, .perform (.cell (.bound 0)) 0 (.variable 1)⟩ := rfl

/-- The actual exported helper's certificate is constructed by the checker
and is the certificate type consumed by lambda-entry/beta relations. -/
example : CoreValueRelation.CallableCertificate CoreExportedFixture.graph 1 3
    (.perform (.cell (.bound 0)) 0 (.variable 1)) :=
  checkFunction_certificate (graph := CoreExportedFixture.graph) (site := 4)
    (checked := ⟨1, 3, .perform (.cell (.bound 0)) 0 (.variable 1)⟩) rfl

/-- A finite reentry-style callable installs its own handler/owner. This shape
example is not claimed to be the export of the Rust reentry experiment. -/
def reentry : Graph := ⟨[
  node 0 .unit,
  node 1 (.request (.user 91 []) 0 0),
  node 2 (.resume 7 4 .consumed 0),
  node 3 (.handler 7 (.user 91 []) 1 [⟨0, .binder ⟨2, .unit⟩, 4, 2⟩]),
  node 4 (.function ⟨9, .unit⟩ 3) (.function .unit .unit [])], 4⟩

def reentryBody : Code := .handle (.user 91 []) (.perform (.user 91 []) 0 .unit)
  (.cons 0 2 (ticket reentry 4) (.resume (ticket reentry 4) .unit) .nil)

example : checkFunction reentry 4 = .ok ⟨9, 3, reentryBody⟩ := rfl

example : checkAmbient reentry 4 [⟨8, 5, 99⟩] = .ok ⟨9, 3, reentryBody⟩ := rfl

/-- A caller collision is retained as a rejection, rather than pruned away. -/
example : checkAmbient reentry 4 [⟨7, 4, 99⟩] = .error (.translation (.duplicateOwner 3 4)) := rfl

example : checkFunction reentry 99 = .error (.missingSite 99) := rfl
example : checkFunction reentry 0 = .error (.notFunction 0) := rfl

def foreignContinuation : Graph := ⟨[
  node 0 .unit,
  node 1 (.resume 7 4 .consumed 0),
  node 2 (.function ⟨9, .unit⟩ 1) (.function .unit .unit [])], 2⟩

example : checkFunction foreignContinuation 2 =
    .error (.translation (.ownerNotActive 1 7 4)) := rfl

/-- The ticket scan is independently negative on raw free-ticket code. -/
example : noOuterTicket 9 (.resume 42 .unit) = false := rfl
example : noOuterTicket 9 (.discard 42) = false := rfl

/-- Complete instance trees and clause ticket fields participate in equality. -/
example : codeEq (.perform (.user 1 [.nominal 7]) 0 .unit)
    (.perform (.user 1 [.resource (.activation 7)]) 0 .unit) = false := rfl

example : clausesEq (.cons 0 1 7 .unit .nil) (.cons 0 1 8 .unit .nil) = false := rfl

end Examples

#print axioms noOuterTicket_sound
#print axioms checkFunction_sound
#print axioms checked_body_fuel_safe
#print axioms codeEq_sound
#print axioms clausesEq_sound
#print axioms codeEq_iff
#print axioms checkAmbient_sound
#print axioms checkAmbient_complete
#print axioms checkFunction_certificate
#print axioms checkAmbient_certificate
#print axioms checked_lambda_evaluate
end Ash.OneShot.CoreCallableChecks
