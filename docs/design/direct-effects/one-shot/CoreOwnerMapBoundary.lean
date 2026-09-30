import CoreStrictStack

/-! Owner-map boundary evidence for TASK-0032, not a semantic discrepancy.

The retained CoreOwnerMapReentry.ash experiment runs through the current
validated Rust CLI to Unit: main's pure f handles E; its clause calls k before
resuming; g captures f and calls it with a terminating callback; main calls
f g. A static handler/owner is reentered while another activation is live,
without recursion or capability escape. This file isolates translation-map
pressure with small finite graphs; it does not equate those graphs with the
export of the experiment or prove source reachability.

Normative static-semantics.md states that anonymous functions, recursive
members and nested handler clauses are barriers for an enclosing continuation
capability. Public translate checks the root and starts with []; that remains
unchanged. Passing a caller-wide owner map into a saved callable component can
introduce a duplicateOwner collision unrelated to its lexical scope. Ordinary
clause code still needs its own lexical owner binding. Dynamic Scope ticket
bindings are distinct from these static translation maps.

The repaired ValueRel/EnvCloses interpreter now uses each callable's certified
empty-map translation and closing derivation. Their owner_transport lemmas
preserve raw lexical meaning across caller maps without transporting source
translation. ComponentWithMaps factors the current code map from the saved
ordinary-frame map; generic beta enters [] while retaining caller frame maps.
CallableBoundary below supplies a finite instance of CallableCertificate.

Required later proofs: existing validate.rs ScopeRequirementKey/requirements_for
analysis (function and recursive-member reject_resume_capture; clause own-resume
removal and foreign-resume rejection) establishes the callable barrier and
noncapture; root translation yields the corresponding empty-map callable body
(or a static map-pruning theorem including duplicate-owner exclusions); lexical
substitution/capture preserves the no-outer-ticket property; saved ordinary
contexts keep their own maps; clause entry extends a fresh lexical binding and
relates its generated binder to the dynamic Scope owner. Current typing and
handler/map validation must be preserved. Removing duplicateOwner checks or
resetting all ordinary clause maps is not justified by this evidence. -/
namespace Ash.OneShot.CoreOwnerMapBoundary
open ScopedExpressions CoreTranslation

/-- A current static callable-site certificate. Empty capability translation
is part of the evidence, rather than an unconstrained owner-map choice or a
future execution assumption. Ordinary variable/resource captures are separate. -/
structure CallableBoundary (graph : CoreSyntax.Graph) (site : Nat)
    (parameter : CoreSyntax.Binder) (body : Nat) (rawBody : Code) : Prop where
  site : ∃ node, graph.node site = some node ∧ node.kind = .function parameter body
  body : ∃ fuel, translateFuel graph fuel [] body = .ok rawBody
  noOuterTicket : ∀ ticket, Syntax.Dependency.ticket ticket ∉
    (Code.lambda parameter.id rawBody).dependencies

theorem CallableBoundary.certificate {graph : CoreSyntax.Graph} {sourceSite bodyIndex : Nat}
    {argument : CoreSyntax.Binder} {raw : Code}
    (boundary : CallableBoundary graph sourceSite argument bodyIndex raw) :
    CoreValueRelation.CallableCertificate graph argument.id bodyIndex raw := by
  obtain ⟨node, known, kind⟩ := boundary.site
  exact ⟨⟨sourceSite, argument, node, known, kind, rfl⟩, boundary.body, boundary.noOuterTicket⟩

namespace Examples
open CoreTranslation.Examples

/-- Root translation succeeds with its checked, empty lexical map. -/
theorem public_owned_handler : translate ownedHandler =
    .ok (.handle exact (.perform exact 0 .unit)
      (.cons 0 2 11 (.resume 11 .unit) .nil)) := rfl

/-- Even a handler-mismatching entry collides before any owner resolution.
Neither a caller's handler identity nor its dynamic ticket repairs the collision. -/
theorem caller_collision (handler ticket : Nat) :
    translateFuel ownedHandler 5 [⟨handler, 4, ticket⟩] 3 =
      .error (.duplicateOwner 3 4) := rfl

/-- Unused does not imply erasable: the exact graph reads its newly installed
owner, while the extraneous collision still makes translation fail. -/
theorem disjoint_caller_entry :
    translateFuel ownedHandler 5 [⟨8, 5, 99⟩] 3 =
      .ok (.handle exact (.perform exact 0 .unit)
        (.cons 0 2 11 (.resume 11 .unit) .nil)) := rfl

private def pureEffect : Instantiation.Effect := .user 91 []
def callableGraph : CoreSyntax.Graph := ⟨[
  node 0 .unit,
  node 1 (.request pureEffect 0 0),
  node 2 (.resume 7 4 .consumed 0),
  node 3 (.handler 7 pureEffect 1 [⟨0, .binder ⟨2, .unit⟩, 4, 2⟩]),
  node 4 (.function ⟨9, .unit⟩ 3) (.function .unit .unit [])], 4⟩
def callableBody : Code := .handle pureEffect (.perform pureEffect 0 .unit)
  (.cons 0 2 (CoreTranslation.ticket callableGraph 4)
    (.resume (CoreTranslation.ticket callableGraph 4) .unit) .nil)

theorem callable_root : translate callableGraph = .ok (.lambda 9 callableBody) := rfl

theorem callable_component_empty : translateFuel callableGraph 6 [] 3 = .ok callableBody := rfl

theorem callable_under_caller_collision (handler ticket : Nat) :
    translateFuel callableGraph 6 [⟨handler, 4, ticket⟩] 3 =
      .error (.duplicateOwner 3 4) := rfl

/-- Exhaustion cannot hide a successful alternative translation at another
fuel: after three structural layers, the same owner collision is inevitable. -/
theorem callable_collision_sufficient (handler ticket fuel : Nat) :
    translateFuel callableGraph (fuel + 3) [⟨handler, 4, ticket⟩] 3 =
      .error (.duplicateOwner 3 4) := rfl

theorem callable_collision_never_succeeds (handler ticket fuel : Nat) (code : Code) :
    translateFuel callableGraph fuel [⟨handler, 4, ticket⟩] 3 ≠ .ok code := by
  cases fuel with
  | zero => intro same; cases same
  | succ fuel =>
    cases fuel with
    | zero => intro same; cases same
    | succ fuel =>
      cases fuel with
      | zero => intro same; cases same
      | succ fuel => rw [show fuel + 1 + 1 + 1 = fuel + 3 by omega, callable_collision_sufficient]; intro same; cases same

theorem callable_boundary : CallableBoundary callableGraph 4 ⟨9, .unit⟩ 3 callableBody := by
  refine ⟨⟨_, rfl, rfl⟩, ⟨6, rfl⟩, ?_⟩
  intro ticket
  simp [callableBody, pureEffect, Code.dependencies, Clauses.dependencies,
    effectAtoms, Syntax.without]

/-- The empty-map callable interpretation really admits a closed lexical value. -/
theorem callable_value : CoreValueRelation.ValueRel callableGraph [] []
    (.closure 9 3 .empty) (.lambda 9 callableBody) := by
  exact .closure callable_component_empty callable_boundary.certificate .empty (by
    simp [ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames,
      Clauses.freeNames, callableBody, pureEffect, Instantiation.Effect.freeNames,
      Code.dependencies, Clauses.dependencies, effectAtoms, Instantiation.Effect.resources, Syntax.without])

/-- The repaired single interpreter represents the callable under a colliding
caller map while preserving its own certified empty-map body interpretation. -/
theorem caller_map_represents_callable (handler ticket : Nat) :
    CoreValueRelation.ValueRel callableGraph [⟨handler, 4, ticket⟩] []
      (.closure 9 3 .empty) (.lambda 9 callableBody) :=
  callable_value.owner_transport _

private def callerOwners : OwnerMap := [⟨7, 4, CoreTranslation.ticket callableGraph 4⟩]
private def reentryBase : CoreMachine.State := { control := .returned .unit }
private def reentryPlain : ScopedExecution.PlainData :=
  ⟨.appArgument (.lambda 9 callableBody),
    .ticket (CoreTranslation.ticket callableGraph 4) 99, .unit, .unit, [], rfl⟩

/-- Actual completed beta from a supplied reentry component enters the empty
callable map while keeping the caller's saved-frame map. No source reachability
or whole dynamic-handler/configuration relation is asserted by this test. -/
theorem callable_reentry_beta :
    CoreStrictStack.ComponentRel callableGraph callerOwners
      { reentryBase with frames := [.applyArgument (.closure 9 3 .empty)] }
      ⟨.app (.lambda 9 callableBody) .unit, reentryPlain.scope, .nil⟩ ∧
    CoreMachine.next callableGraph { reentryBase with frames := [.applyArgument (.closure 9 3 .empty)] } =
      .stepped { reentryBase with control := .evaluate 3 (.binding 9 .unit .empty) } ∧
    ScopedExecution.RawStep
      ⟨.app (.lambda 9 callableBody) .unit, reentryPlain.scope, .nil⟩
      ⟨callableBody.subst 9 .unit, .none, .nil⟩ [] [] ∧
    CoreStrictStack.ComponentWithMaps callableGraph [] callerOwners
      { reentryBase with control := .evaluate 3 (.binding 9 .unit .empty) }
      ⟨callableBody.subst 9 .unit, .none, .nil⟩ :=
  CoreStrictStack.beta_complete (base := reentryBase)
    (callable_value.owner_transport callerOwners) CoreValueRelation.ValueRel.unit
    reentryPlain rfl CoreStrictStack.PushedRel.nil Execution.Scope.none

/-- Resetting every component map would lose legal clause completion. -/
theorem clause_requires_lexical_binding :
    translateFuel ownedHandler 2 [] 2 = .error (.ownerNotActive 2 7 4) := rfl

theorem clause_with_lexical_binding :
    translateFuel ownedHandler 2 [⟨7, 4, 11⟩] 2 = .ok (.resume 11 .unit) := rfl

/-- One static translated binder can refer to different dynamic activations.
These Scope mappings cannot be inserted as ambient lexical OwnerMap entries. -/
theorem separate_dynamic_activations :
    Execution.Scope.resolve (.ticket 11 99) 11 = some 99 ∧
    Execution.Scope.resolve (.ticket 11 100) 11 = some 100 := ⟨rfl, rfl⟩

end Examples

#print axioms Examples.public_owned_handler
#print axioms Examples.caller_collision
#print axioms Examples.disjoint_caller_entry
#print axioms Examples.callable_root
#print axioms Examples.callable_component_empty
#print axioms Examples.callable_under_caller_collision
#print axioms Examples.callable_collision_sufficient
#print axioms Examples.callable_collision_never_succeeds
#print axioms Examples.callable_boundary
#print axioms Examples.callable_value
#print axioms Examples.caller_map_represents_callable
#print axioms Examples.callable_reentry_beta
#print axioms Examples.clause_requires_lexical_binding
#print axioms Examples.clause_with_lexical_binding
#print axioms Examples.separate_dynamic_activations
end Ash.OneShot.CoreOwnerMapBoundary
