import SourceConsumingCaptureBounds

/-! A handler installed around resumption must cover the continuation it may
intercept, not just offer the requested operation. Finite source bounds imply
the corresponding check for every retained source satisfying those bounds. -/
namespace Ash.OneShot.SourceScheduledRetainedInterfaces
open SourceContextualHints (Hints Requirement)
open SourceDependencyCapture (Scope)
open SourceRetainedPlans (Forest)
open SourceHandlerRequirements (outwardRequirements)

private theorem outward_append (first second : Scope) (required : List Requirement) :
    outwardRequirements (first.append second) required =
      outwardRequirements second (outwardRequirements first required) := by
  simp only [outwardRequirements, List.filter_filter]
  congr 1
  funext request
  simpa only [Bool.and_comm] using SourceScheduledCallbackInterfaces.reaches_append first (tail := second) (effect := request.1)

private theorem outward_union (scope : Scope) (first second : List Requirement) :
    outwardRequirements scope (first ++ second) =
      outwardRequirements scope first ++ outwardRequirements scope second := List.filter_append first second

private theorem outward_mono (scope : Scope) (included : first ⊆ second) :
    outwardRequirements scope first ⊆ outwardRequirements scope second := by
  intro request member
  obtain ⟨member, passed⟩ := List.mem_filter.mp member
  exact List.mem_filter.mpr ⟨included member, passed⟩

/-- The receiving suffix filters each exposed request in the prefix before
its own requirements are added. This preserves interpretation order. -/
theorem Interfaces.exposed_append {frontHints : Hints frontScope} {tailHints : Hints tailScope}
    {front : Forest frontHints} {tail : Forest tailHints}
    (first : Interfaces world front) (second : Interfaces world tail) :
    (first.append second).exposed = outwardRequirements tailScope first.exposed ++ second.exposed := by
  induction first with
  | nil => rfl
  | plain rest required footprint declared next ih =>
      change outwardRequirements ((_: Scope).append tailScope) required ++ (next.append second).exposed =
        outwardRequirements tailScope (outwardRequirements _ required ++ next.exposed) ++ second.exposed
      rw [ih, outward_append, outward_union, List.append_assoc]
      rfl
  | handler rest next ih =>
      change outwardRequirements ((_: Scope).append tailScope) _ ++ (next.append second).exposed =
        outwardRequirements tailScope (outwardRequirements _ _ ++ next.exposed) ++ second.exposed
      rw [ih, outward_append, outward_union, List.append_assoc]
      rfl
  | cell next ih | running next ih | spent next ih => exact ih
  | cleanup rest required footprint declared next ih =>
      change outwardRequirements ((Scope.running _).append tailScope) required ++ (next.append second).exposed =
        outwardRequirements tailScope (outwardRequirements (Scope.running _) required ++ next.exposed) ++ second.exposed
      rw [ih, outward_append, outward_union, List.append_assoc]
      rfl
  | live rest saved next ihSaved ih =>
      change outwardRequirements ((_: Scope).append tailScope) saved.exposed ++ (next.append second).exposed =
        outwardRequirements tailScope (outwardRequirements _ saved.exposed ++ next.exposed) ++ second.exposed
      rw [ih, outward_append, outward_union, List.append_assoc]
      rfl

/-- The unknown captured source is represented only by its declared bound.
The syntactically known caller contributes its own exposed requirements. -/
theorem Interfaces.recomposition_bound {frontHints : Hints frontScope} {tailHints : Hints tailScope}
    {front : Forest frontHints} {tail : Forest tailHints}
    (first : Interfaces world front) (second : Interfaces world tail)
    (bounded : first.exposed ⊆ resumeRequired)
    (accepted : outwardRequirements tailScope resumeRequired ++ second.exposed ⊆ offeredRequired) :
    (first.append second).exposed ⊆ offeredRequired := by
  rw [first.exposed_append second]
  exact (ScopedExpressions.append_subset (outward_mono tailScope bounded) (List.Subset.refl _)).trans accepted

end Ash.OneShot.SourceScheduledRetainedInterfaces

namespace Ash.OneShot.SourceConsumingClauseAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceHandlerRequirements (outwardRequirements)

/-- Source-level resume bounds cover any later captured source, after the
newly installed caller prefix filters requests. The finite premise contains
declared bounds and caller syntax, not a checked future captured body. -/
theorem Bounds.resume_recomposition {frontHints : Hints frontScope} {tailHints : Hints tailScope}
    {front : Forest frontHints} {tail : Forest tailHints}
    (bounds : Bounds) (first : Interfaces world front) (caller : Interfaces world tail)
    (bounded : first.exposed ⊆ resumeRequired)
    (accepted : outwardRequirements tailScope resumeRequired ++ caller.exposed ⊆ bounds.resume) :
    bounds.check ⟨true, false⟩ (first.append caller).exposed closing = true := by
  apply bounds.check_iff _ |>.mpr
  exact ⟨fun _ => first.recomposition_bound caller bounded accepted, by intro impossible; cases impossible⟩

/-- For a handler around resumption, source admission itself supplies the
finite recomposition condition. The intercepted mode uses the bounds carried
by that exact source handler, including after requirement weakening. -/
theorem Admitted.handler_resume_recomposition
    [declarations : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
    {plans : SourceDeclarationPlans.ClausePlans clauses families} {bounds : ClauseBounds plans}
    {evidence : declarations.accepts handlerRequired plans}
    (admitted : Admitted rights resumeRequired closeRequired
      (Body.handler (effect := effect) (table := table) bounds evidence
        (Body.resume (world := world) (owner := owner))) required)
    (found : bounds.lookup operation held = some selected)
    {frontHints : Hints frontScope} {front : Forest frontHints}
    (inside : Interfaces world front) (bounded : inside.exposed ⊆ resumeRequired) :
    selected.check ⟨true, false⟩
      (inside.append (Interfaces.handler (effect := effect) (table := table) (families := families)
        (required := handlerRequired) .nil .nil)).exposed closing = true := by
  obtain ⟨bodyRequired, source, covered⟩ := admitted.handler_bounds
  have selectedBound := bounds.acceptsResume_lookup covered found
  apply selected.resume_recomposition inside _ (bounded.trans source.resume_requirements)
  intro request member
  apply selectedBound
  rcases List.mem_append.mp member with first | second
  · exact List.mem_append_right _ first
  · change request ∈ outwardRequirements .nil handlerRequired ++ [] at second
    have member := (List.mem_append.mp second).resolve_right (by simp)
    exact List.mem_append_left _ (List.mem_filter.mp member).1

namespace ReinterpretationExamples
open SourceDependencyCapture.Examples (effectF resumeTable)
open SourceScheduledClauseHandlers.Examples (innerFamilies innerPlans resumeBodies)

def effectG : Instance := .user 94 []
def bodies (owner : Nat) : Body [] owner (resumeBodies owner) := .sequence [] .pure .pure .resume
def declarations : Declarations [] innerPlans := .cons (.available bodies) (.available bodies) .nil
def emptyBounds : ClauseBounds innerPlans := .cons (.available ⟨[], []⟩) (.available ⟨[], []⟩) .nil

theorem empty_declaration_admitted : Bounded emptyBounds declarations [] := by
  have mode : BoundedMode (ScopedExpressions.Code.resume 3 .unit).requiredActions (.available ⟨[], []⟩) (.available bodies) [] :=
    .available (.available (fun _ => .sequence (.resume rfl))) (fun _ => .sequence .resume)
  exact .cons (body := .resume 3 .unit) mode mode .nil

def handlerHints : Hints (.handler effectF resumeTable innerFamilies .nil) := .handler [] .nil
def handler : Forest handlerHints := .handler .nil
def handlerInterface : Interfaces [] handler := .handler .nil .nil
def futureHints : Hints (.plain (.request effectG 0) .nil) := .plain .nil
def future : Forest futureHints := .plain .request .nil
def futureInterface : Interfaces [] future := .plain .nil [(effectG, 0)] .request .request .nil
def captured : Forest (futureHints.append handlerHints) := future.append handler
def capturedInterface : Interfaces [] captured := futureInterface.append handlerInterface

/-- The ordinary operation capability and the declaration's own admission
both hold, but the handler's empty resume bound does not cover the G tail. -/
theorem operation_available_but_bound_fails :
    SourceContextualHints.checkCapability (.handler effectF resumeTable innerFamilies .nil) effectF 0 = true ∧
      emptyBounds.check 0 false ⟨true, false⟩ capturedInterface.exposed [] = false := ⟨rfl, rfl⟩

/-- Checking the declared continuation interface at installation detects the
failure without inspecting the unknown captured code. -/
theorem empty_bound_rejected_at_installation :
    ¬ (outwardRequirements (.handler effectF resumeTable innerFamilies .nil)
      [(effectF, 0), (effectG, 0)] ++ handlerInterface.exposed ⊆ ([] : List SourceContextualHints.Requirement)) := by
  intro included
  have impossible := included (by decide : (effectG, 0) ∈
    outwardRequirements (.handler effectF resumeTable innerFamilies .nil)
      [(effectF, 0), (effectG, 0)] ++ handlerInterface.exposed)
  cases impossible

theorem declared_bound_covers_reinterpretation :
    (Bounds.mk [(effectG, 0)] []).check ⟨true, false⟩ capturedInterface.exposed [] = true := by
  apply Bounds.resume_recomposition (resumeRequired := [(effectF, 0), (effectG, 0)])
    _ futureInterface handlerInterface
  · intro request member
    change request ∈ [(effectG, 0)] at member
    have same := List.mem_singleton.mp member
    subst request
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.Subset.refl _

/-- The bounds are explicit syntax annotations at this nested installation. -/
def installer (bounds : ClauseBounds innerPlans) (owner : Nat) : Body [] owner
    (SourceDeclarationPlans.Plan.handler (effect := effectF) (table := resumeTable) [] innerPlans
      (.invoke (key := ⟨owner, .resume⟩))) :=
  .handler bounds SourceScheduledClauseHandlers.Examples.inner_declarations .resume

def gBounds : ClauseBounds innerPlans :=
  .cons (.available ⟨[(effectG, 0)], []⟩) (.available ⟨[(effectG, 0)], []⟩) .nil

theorem installer_admitted :
    Admitted ⟨true, false⟩ [(effectF, 0), (effectG, 0)] [] (installer gBounds 19) [(effectG, 0)] :=
  .handler (.resume rfl) rfl rfl

/-- The previously failing bounds are now rejected by the structural source
judgment itself, for any claimed outer requirements. -/
theorem empty_installer_rejected :
    ¬ Admitted ⟨true, false⟩ [(effectF, 0), (effectG, 0)] [] (installer emptyBounds 19) required := by
  intro source
  have accepted := source.handler_resume_recomposition (operation := 0) (held := false)
    (selected := ⟨[], []⟩) (closing := []) rfl futureInterface
    (show futureInterface.exposed ⊆ [(effectF, 0), (effectG, 0)] from by
      intro request member
      change request ∈ [(effectG, 0)] at member
      exact List.mem_cons_of_mem _ member)
  cases accepted

end ReinterpretationExamples
end Ash.OneShot.SourceConsumingClauseAnnotations

#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.exposed_append
#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.recomposition_bound
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Bounds.resume_recomposition
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.ReinterpretationExamples.empty_declaration_admitted
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.ReinterpretationExamples.operation_available_but_bound_fails
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.ReinterpretationExamples.empty_bound_rejected_at_installation
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.ReinterpretationExamples.declared_bound_covers_reinterpretation

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Admitted.handler_resume_recomposition
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.ReinterpretationExamples.installer_admitted
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.ReinterpretationExamples.empty_installer_rejected
