import SourcePlannedChecks
import SourcePlannedSources

/-! Ordered composition of strengthened pending checks. Scope associativity
is reused; the additional proof retains the exact handler annotations and
pending plan witnesses, including inside dormant captures. Resume and disposal
clauses are constructed from their retained parts and independent invocation
capabilities. Deriving those parts at every source capture remains open. -/
namespace Ash.OneShot.SourcePlannedRecomposition
open SourceContextualHints (Hints)
open SourcePlannedChecks (Local Pending)
open SourceDependencyChecks (scope_append_assoc)

theorem lift_heq {shape : SourceDependencyCapture.Scope → SourceDependencyCapture.Scope} {first : Hints firstScope} {second : Hints secondScope}
    (same : firstScope = secondScope) (hints : HEq first second)
    (lift : ∀ {scope}, Hints scope → Hints (shape scope)) : HEq (lift first) (lift second) := by
  cases same
  cases hints
  rfl

theorem hints_append_assoc (first : Hints firstScope) (second : Hints secondScope) (third : Hints thirdScope) :
    HEq ((first.append second).append third) (first.append (second.append third)) := by
  induction first with
  | nil => rfl
  | plain rest ih => exact lift_heq (scope_append_assoc _ _ _) ih (fun hints => .plain hints)
  | handler required rest ih => exact lift_heq (scope_append_assoc _ _ _) ih (fun hints => .handler required hints)
  | cell rest ih => exact lift_heq (scope_append_assoc _ _ _) ih (fun hints => .cell hints)
  | cleanup rest ih => exact lift_heq (scope_append_assoc _ _ _) ih (fun hints => .cleanup hints)
  | running rest ih => exact lift_heq (scope_append_assoc _ _ _) ih (fun hints => .running hints)
  | live saved rest ihSaved ihRest => exact lift_heq (scope_append_assoc _ _ _) ihRest (fun hints => .live saved hints)
  | spent rest ih => exact lift_heq (scope_append_assoc _ _ _) ih (fun hints => .spent hints)

private theorem predicate_congr {first : Hints firstScope} {second : Hints secondScope}
    (same : firstScope = secondScope) (hints : HEq first second)
    (predicate : ∀ {scope}, Hints scope → Prop) : predicate first ↔ predicate second := by
  cases same
  cases hints
  rfl

theorem local_append_assoc (first : Hints firstScope) (second : Hints secondScope) (third : Hints thirdScope) :
    Local outward actions phases world plan ((first.append second).append third) ↔
      Local outward actions phases world plan (first.append (second.append third)) :=
  predicate_congr (scope_append_assoc _ _ _) (hints_append_assoc first second third) (fun hints => Local outward actions phases world plan hints)

theorem running_append_assoc (first : Hints firstScope) (second : Hints secondScope) (third : Hints thirdScope) :
    Local outward actions phases world plan (.running ((first.append second).append third)) ↔
      Local outward actions phases world plan (.running (first.append (second.append third))) :=
  predicate_congr (scope_append_assoc _ _ _) (hints_append_assoc first second third) (fun hints => Local outward actions phases world plan (.running hints))

theorem pending_outside_assoc (first : Hints firstScope) (second : Hints secondScope) (third : Hints thirdScope) :
    Pending outward actions phases world saved ((first.append second).append third) ↔
      Pending outward actions phases world saved (first.append (second.append third)) :=
  predicate_congr (scope_append_assoc _ _ _) (hints_append_assoc first second third) (fun hints => Pending outward actions phases world saved hints)

/-- Split and join the same annotated forest. Every pending expression and
callback retains its plan, and dormant branches retain their complete suffix. -/
theorem pending_append_iff (first : Hints firstScope) (second : Hints secondScope) (outside : Hints outsideScope) :
    Pending outward actions phases world (first.append second) outside ↔
      Pending outward actions phases world first (second.append outside) ∧
      Pending outward actions phases world second outside := by
  induction first with
  | nil => exact ⟨fun checked => ⟨.nil, checked⟩, fun ⟨_, checked⟩ => checked⟩
  | plain rest ih =>
      constructor
      · intro checked; cases checked with
        | plain code tail =>
            obtain ⟨inside, remaining⟩ := ih.mp tail
            exact ⟨.plain ((local_append_assoc _ _ _).mp code) inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | plain code tail => exact .plain ((local_append_assoc _ _ _).mpr code) (ih.mpr ⟨tail, remaining⟩)
  | cleanup rest ih =>
      constructor
      · intro checked; cases checked with
        | cleanup callback tail =>
            obtain ⟨inside, remaining⟩ := ih.mp tail
            exact ⟨.cleanup ((running_append_assoc _ _ _).mp callback) inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | cleanup callback tail => exact .cleanup ((running_append_assoc _ _ _).mpr callback) (ih.mpr ⟨tail, remaining⟩)
  | live saved rest ihSaved ihRest =>
      constructor
      · intro checked; cases checked with
        | live saved tail =>
            obtain ⟨inside, remaining⟩ := ihRest.mp tail
            exact ⟨.live ((pending_outside_assoc _ _ _).mp saved) inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | live saved tail => exact .live ((pending_outside_assoc _ _ _).mpr saved) (ihRest.mpr ⟨tail, remaining⟩)
  | handler required rest ih =>
      constructor
      · intro checked; cases checked with
        | handler tail => obtain ⟨inside, remaining⟩ := ih.mp tail; exact ⟨.handler inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | handler tail => exact .handler (ih.mpr ⟨tail, remaining⟩)
  | cell rest ih =>
      constructor
      · intro checked; cases checked with
        | cell tail => obtain ⟨inside, remaining⟩ := ih.mp tail; exact ⟨.cell inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | cell tail => exact .cell (ih.mpr ⟨tail, remaining⟩)
  | running rest ih =>
      constructor
      · intro checked; cases checked with
        | running tail => obtain ⟨inside, remaining⟩ := ih.mp tail; exact ⟨.running inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | running tail => exact .running (ih.mpr ⟨tail, remaining⟩)
  | spent rest ih =>
      constructor
      · intro checked; cases checked with
        | spent tail => obtain ⟨inside, remaining⟩ := ih.mp tail; exact ⟨.spent inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | spent tail => exact .spent (ih.mpr ⟨tail, remaining⟩)

theorem pending_capture {saved : Hints savedScope} {tail : Hints tailScope}
    (checked : Pending outward actions phases world (saved.append tail) outside) :
    Pending outward actions phases world (.live (owner := owner) saved tail) outside :=
  .live ((pending_append_iff _ _ _).mp checked).1 ((pending_append_iff _ _ _).mp checked).2

theorem hints_append_nil (hints : Hints scope) : HEq (hints.append .nil) hints := by
  induction hints with
  | nil => rfl
  | plain rest ih => exact lift_heq (SourceDependencyProjection.scope_append_nil _) ih (fun hints => .plain hints)
  | handler required rest ih => exact lift_heq (SourceDependencyProjection.scope_append_nil _) ih (fun hints => .handler required hints)
  | cell rest ih => exact lift_heq (SourceDependencyProjection.scope_append_nil _) ih (fun hints => .cell hints)
  | cleanup rest ih => exact lift_heq (SourceDependencyProjection.scope_append_nil _) ih (fun hints => .cleanup hints)
  | running rest ih => exact lift_heq (SourceDependencyProjection.scope_append_nil _) ih (fun hints => .running hints)
  | live saved rest ihSaved ihRest => exact lift_heq (SourceDependencyProjection.scope_append_nil _) ihRest (fun hints => .live saved hints)
  | spent rest ih => exact lift_heq (SourceDependencyProjection.scope_append_nil _) ih (fun hints => .spent hints)

theorem pending_outside_nil (outside : Hints scope) :
    Pending outward actions phases world saved (outside.append .nil) ↔ Pending outward actions phases world saved outside :=
  predicate_congr (SourceDependencyProjection.scope_append_nil _) (hints_append_nil outside)
    (fun hints => Pending outward actions phases world saved hints)

theorem local_append_nil (hints : Hints scope) :
    Local outward actions phases world plan (hints.append .nil) ↔ Local outward actions phases world plan hints :=
  predicate_congr (SourceDependencyProjection.scope_append_nil _) (hints_append_nil hints)
    (fun hints => Local outward actions phases world plan hints)

open SourceDependencyProjection (project project_append project_select)
open SourceContextualHints (checkCapability checkRequirements)
open SourceContextualHintChecking (Compatible check_iff check_append)
open SourceContextualInvocationHints (forClosing)

/-- Spent markers do not change the selected operation's advertised capability;
reuse the earlier exact selection projection rather than another lookup proof. -/
theorem capability_project : checkCapability (project scope) effect operation = checkCapability scope effect operation := by
  unfold checkCapability
  rw [project_select]
  cases SourceDependencyCapture.select effect operation scope with
  | none => rfl
  | some selected => cases selected <;> rfl

theorem requirements_project : checkRequirements (project scope) required = checkRequirements scope required := by
  simp only [checkRequirements, capability_project]

private theorem requirements_congr (same : project first = project second) :
    checkRequirements first required = checkRequirements second required := by
  rw [← requirements_project (scope := first), ← requirements_project (scope := second), same]

theorem hints_outside_project (hints : Hints scope) (same : project first = project second) :
    hints.check first = hints.check second := by
  induction hints generalizing first second with
  | nil => rfl
  | plain rest ih | cell rest ih | cleanup rest ih | running rest ih | spent rest ih => exact ih same
  | handler required rest ih =>
      simp only [Hints.check]
      congr 1
      · apply requirements_congr
        simp only [project_append, same]
      · exact ih same
  | live saved rest ihSaved ihRest =>
      simp only [Hints.check]
      congr 1
      · apply ihSaved
        simp only [project_append, same]
      · exact ihRest same

/-- Restoring at the head preserves installed-handler compatibility. This is
independent of permission, phase and checking the retained source programs. -/
theorem resume_compatible {saved : Hints savedScope} {tail : Hints tailScope}
    (compatible : Compatible (.live (owner := owner) saved tail) .nil) :
    Compatible (saved.append (.spent (owner := owner) tail)) .nil := by
  apply (check_iff _).mp
  have before := (check_iff _).mpr compatible
  have outsideSame : saved.check ((SourceDependencyCapture.Scope.spent owner tailScope).append .nil) =
      saved.check (tailScope.append .nil) := hints_outside_project saved (by simp only [project_append, project])
  rw [check_append, outsideSame]
  exact before

/-- The scheduled closing annotation contains no installed handlers. Callback
bodies still require their separate strengthened Pending checks. -/
theorem closing_check (hints : Hints scope) : (forClosing hints).check outside = true := by
  induction hints generalizing outside with
  | nil => rfl
  | plain rest ih | handler required rest ih | cell rest ih | cleanup rest ih | running rest ih | spent rest ih => exact ih
  | live saved rest ihSaved ihRest =>
      change ((forClosing saved).append (.running (forClosing rest))).check outside = true
      rw [check_append]
      rw [Bool.and_eq_true]
      exact ⟨ihSaved, ihRest⟩

theorem dispose_compatible {saved : Hints savedScope} {tail : Hints tailScope}
    (compatible : Compatible tail .nil) :
    Compatible ((forClosing saved).append (.running (.spent (owner := owner) tail))) .nil := by
  apply (check_iff _).mp
  simp only [check_append, closing_check, Hints.check, Bool.true_and]
  exact (check_iff _).mpr compatible

/-- Construct the restored pending judgment from the two retained source
pieces. Their checks use the receiving scope and the already spent phase. -/
theorem pending_resume {saved : Hints savedScope} {tail : Hints tailScope}
    (inside : Pending outward actions phases world saved (.spent (owner := owner) tail))
    (waiting : Pending outward actions phases world tail .nil) :
    Pending outward actions phases world (saved.append (.spent (owner := owner) tail)) .nil :=
  (pending_append_iff _ _ _).mpr ⟨(pending_outside_nil _).mpr inside, .spent waiting⟩

theorem pending_dispose {saved : Hints savedScope} {tail : Hints tailScope}
    (closing : Pending outward actions phases world (forClosing saved) (.running (.spent (owner := owner) tail)))
    (waiting : Pending outward actions phases world tail .nil) :
    Pending outward actions phases world ((forClosing saved).append (.running (.spent (owner := owner) tail))) .nil :=
  (pending_append_iff _ _ _).mpr ⟨(pending_outside_nil _).mpr closing, .running (.spent waiting)⟩

/-- A head resume clause follows from structural checks of the retained code,
independent permission and availability, and installed-handler compatibility.
No check of the complete successor is assumed. -/
theorem resume_clause {saved : Hints savedScope} {tail : Hints tailScope}
    (known : actions owner = some rights) (permission : rights.resume = true)
    (available : phases owner = .available)
    (inside : Pending outward actions (OwnerPhaseTransitions.spend phases owner) world saved (.spent (owner := owner) tail))
    (waiting : Pending outward actions (OwnerPhaseTransitions.spend phases owner) world tail .nil)
    (compatible : Compatible (.live (owner := owner) saved tail) .nil) :
    Local outward actions phases world (.invoke (key := ⟨owner, .resume⟩)) (.live (owner := owner) saved tail) := by
  let selected : SourceContextualInvocationHints.Selection := ⟨⟨.nil, savedScope, tailScope⟩, .nil, saved, tail⟩
  refine .resume (after := selected.resumed owner) ?_ (pending_resume inside waiting)
  exact .checked (by simp [SourceContextualInvocationHints.findOwner, selected])
    (.checked .hit known permission available) (resume_compatible compatible)

/-- Disposal independently checks protection and the existing closing route.
The callback judgments are checked at their actual scheduled receiving scope. -/
theorem dispose_clause {saved : Hints savedScope} {tail : Hints tailScope}
    (known : actions owner = some rights) (permission : rights.dispose = true)
    (available : phases owner = .available) (unprotected : savedScope.held = false)
    (route : SourceRecursiveRoutes.Closing outward savedScope.shape [] [])
    (closing : Pending outward actions (OwnerPhaseTransitions.spend phases owner) world
      (forClosing saved) (.running (.spent (owner := owner) tail)))
    (waiting : Pending outward actions (OwnerPhaseTransitions.spend phases owner) world tail .nil)
    (compatible : Compatible tail .nil) :
    Local outward actions phases world (.invoke (key := ⟨owner, .dispose⟩)) (.live (owner := owner) saved tail) := by
  let selected : SourceContextualInvocationHints.Selection := ⟨⟨.nil, savedScope, tailScope⟩, .nil, saved, tail⟩
  refine .dispose (after := selected.disposed owner) ?_ (pending_dispose closing waiting)
  exact .checked (by simp [SourceContextualInvocationHints.findOwner, selected])
    (.checked .hit known permission available unprotected route) (dispose_compatible compatible)

/-- A builtin request cannot select a disposing handler. Reuse the existing
capture guard and keep the stronger callback obligation vacuous by lookup. -/
theorem builtin_request [evidence : SourcePlannedChecks.DeclarationPolicy] {hints : Hints scope}
    (found : SourceDependencyCapture.select effect operation scope = some (.builtin identity)) :
    Local outward actions phases world (.request (effect := effect) (operation := operation)) hints := by
  have projected : SourceDependencyCapture.select effect operation (project scope) = some (.builtin identity) := by
    rw [project_select, found]
    rfl
  refine .request (.request (.builtin projected) ?_ ?_) ?_
  · intro captured tail contract modes selected
    rw [projected] at selected
    cases selected
  · intro captured tail contract modes selected
    rw [projected] at selected
    cases selected
  · intro captured tail saved waiting contract modes same selected
    rw [found] at selected
    cases selected

/-- Reuse the earlier request-prefix proof at the stronger source layer.
The capability supplies a builtin or a non-disposing handler, so this prefix
adds no callback-scheduling premise. It does not duplicate an owner. -/
theorem request_prefix {saved : Hints savedScope} {tail : Hints tailScope}
    {plan : SourceDeclarationPlans.Plan dependencies}
    (capability : SourceContextualClauses.RequestCapability effect operation tailScope)
    (next : Local outward actions phases world plan (.live (owner := owner) saved tail)) :
    Local outward actions phases world (.sequence (.sequence .pure (.request (effect := effect) (operation := operation))) plan)
      (.live (owner := owner) saved tail) := by
  refine .sequence (.sequence .pure (.request capability.request ?_)) next
  intro captured outside capturedHints outsideHints contract modes same selected disposes
  cases capability with
  | builtin found =>
      simp only [SourceDependencyCapture.select, found, Option.map_some,
        SourceDependencyCapture.Selection.prepend] at selected
      cases selected
  | handler found resumesOnly rows bodies =>
      simp only [SourceDependencyCapture.select, found, Option.map_some,
        SourceDependencyCapture.Selection.prepend, Option.some.injEq] at selected
      cases selected
      simp [resumesOnly] at disposes

namespace Examples
open ScopedExpressions ScopedExecution
open SourceContextualInvocations.Examples (actions disposalStack tables families required)
open SourcePlannedTyping (Value)

def callbackPlan : SourceDeclarationPlans.Plan
    (.sequence (.sequence .pure (.request (.cell 4) 0)) .pure) :=
  .sequence (.sequence .pure .request) .pure

def operations : SourcePlannedTyping.Operations
  | .cell identity, 0 => some (.reference identity, .integer)
  | _, _ => none

def callbackRequirements : RecursiveRequirements.Requirements [] :=
  .sequence (.emitAfter (.request [] []) [] [⟨.cell 4, 0, false⟩]) (.request [] [])

/-- Authenticate the complete existing callback, including its bind and
operand evaluation, against the same plan used by the pending check. -/
theorem callback_source :
    SourcePlannedSources.Expression operations policy contracts [4] allowed scope environment
      ScopedPorts.CompletionExamples.callback
      (.function .unit .unit [.cell 4] [⟨.cell 4, 0, false⟩] (SourcePlanSignatures.signature callbackPlan))
      [] (.request [] []) .pure := by
  apply SourcePlannedSources.Expression.lambda (bodyRequirements := callbackRequirements)
  · exact .bind (.perform rfl (by simp) (.reference (by simp))
      (by simp [Value.erase, SourceDependencyAnnotations.Value.erase, ScopedPorts.InWorld,
        CoherentSourceTypes.Value.port, ScopedPorts.Port.resources])) .unit
  · exact .sequence (.emitAfter (layers := []) (.request (layers := []))) (.request (layers := []))
  · simp [Value.erase, SourceDependencyAnnotations.Value.erase, ScopedPorts.InWorld,
      CoherentSourceTypes.Value.port, ScopedPorts.Port.resources, Instance.resources]
  · intro request member
    cases List.mem_singleton.mp member
    exact List.mem_cons_self

def nestedScope : SourceDependencyCapture.Scope := .live 6
  (.cleanup [.cell 4] (.sequence (.sequence .pure (.request (.cell 4) 0)) .pure) .nil) (.cell 4 .nil)
def nestedHints : Hints nestedScope := .live (.cleanup .nil) (.cell .nil)
def disposalHints : Hints (.live 8 nestedScope .nil) := .live nestedHints .nil

theorem nested_disposal_matches :
    SourceContextualHintChecking.Matches tables families required disposalHints disposalStack :=
  .live (.live (.cleanup (action := ScopedPorts.CompletionExamples.action) .nil) (.cell .nil)) .nil

/-- The existing dormant-owner example now checks its actual cell callback
under the scheduled closing stack, including the outer spent boundary. -/
theorem nested_closing_pending :
    Pending [] actions (OwnerPhaseTransitions.spend (OwnerPhaseTransitions.available [8, 6]) 8) [4]
      (forClosing nestedHints) (.running (.spent (owner := 8) .nil)) :=
  .cleanup (plan := callbackPlan) (.sequence (.sequence .pure (builtin_request rfl)) .pure) (.running (.cell .nil))

theorem nested_disposal_checked :
    Local [] actions (OwnerPhaseTransitions.available [8, 6]) [4]
      (.invoke (key := ⟨8, .dispose⟩)) disposalHints :=
  dispose_clause rfl rfl (by rfl) rfl
    (SourceDependencyCapture.check_closing_iff.mp (by rfl)) nested_closing_pending .nil .nil

/-- Reuse the actual disposal/ownership theorem with the stronger source
check. Owner 8 is consumed and owner 6 remains accounted for by the plan. -/
theorem nested_disposal_source_step :
    ∃ after : SourceContextualInvocationHints.Annotated, ∃ afterStack captured plan,
      Pending [] actions (OwnerPhaseTransitions.spend (OwnerPhaseTransitions.available [8, 6]) 8) [4] after.hints .nil ∧
      RawStep ⟨.discard 0, .ticket 0 8, disposalStack⟩ ⟨.unit, .ticket 0 8, afterStack⟩ [.close 20] [.ticket 8] ∧
      SourceContextualHintChecking.Matches tables families required after.hints afterStack ∧
      SourceContextualForest.Forest [] tables families afterStack after.scope .nil ∧
      makePlan captured = some plan ∧ (planOwners (plan.map CloseEntry.erase)).Perm captured.erase.owners ∧
      (ownedTickets disposalStack).Perm (8 :: ownedTickets afterStack) ∧
      OwnerPhaseTransitions.Trace (OwnerPhaseTransitions.available (ownedTickets disposalStack)) [8]
        (OwnerPhaseTransitions.available (ownedTickets afterStack)) :=
  nested_disposal_checked.dispose_step nested_disposal_matches
    (fun handler member => by cases member) (by decide) rfl

end Examples

end Ash.OneShot.SourcePlannedRecomposition

#print axioms Ash.OneShot.SourcePlannedRecomposition.hints_append_assoc
#print axioms Ash.OneShot.SourcePlannedRecomposition.local_append_assoc
#print axioms Ash.OneShot.SourcePlannedRecomposition.running_append_assoc
#print axioms Ash.OneShot.SourcePlannedRecomposition.pending_outside_assoc
#print axioms Ash.OneShot.SourcePlannedRecomposition.pending_append_iff
#print axioms Ash.OneShot.SourcePlannedRecomposition.pending_capture

#print axioms Ash.OneShot.SourcePlannedRecomposition.hints_append_nil

#print axioms Ash.OneShot.SourcePlannedRecomposition.pending_outside_nil
#print axioms Ash.OneShot.SourcePlannedRecomposition.local_append_nil

#print axioms Ash.OneShot.SourcePlannedRecomposition.capability_project

#print axioms Ash.OneShot.SourcePlannedRecomposition.requirements_project

#print axioms Ash.OneShot.SourcePlannedRecomposition.hints_outside_project

#print axioms Ash.OneShot.SourcePlannedRecomposition.resume_compatible

#print axioms Ash.OneShot.SourcePlannedRecomposition.closing_check

#print axioms Ash.OneShot.SourcePlannedRecomposition.dispose_compatible
#print axioms Ash.OneShot.SourcePlannedRecomposition.pending_resume
#print axioms Ash.OneShot.SourcePlannedRecomposition.pending_dispose
#print axioms Ash.OneShot.SourcePlannedRecomposition.resume_clause
#print axioms Ash.OneShot.SourcePlannedRecomposition.dispose_clause
#print axioms Ash.OneShot.SourcePlannedRecomposition.builtin_request
#print axioms Ash.OneShot.SourcePlannedRecomposition.request_prefix
#print axioms Ash.OneShot.SourcePlannedRecomposition.Examples.callback_source
#print axioms Ash.OneShot.SourcePlannedRecomposition.Examples.nested_disposal_matches
#print axioms Ash.OneShot.SourcePlannedRecomposition.Examples.nested_closing_pending
#print axioms Ash.OneShot.SourcePlannedRecomposition.Examples.nested_disposal_checked
#print axioms Ash.OneShot.SourcePlannedRecomposition.Examples.nested_disposal_source_step

#print axioms Ash.OneShot.SourcePlannedRecomposition.lift_heq
