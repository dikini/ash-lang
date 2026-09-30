import SourceConsumingClauseAnnotations
import SourceScheduledInterfaceRequirements

/-! Source-facing operation bounds for captured continuations. A clause checks
finite resume/close interfaces at its syntactically generated caller contexts.
The retained-source transport theorem then derives the concrete capture checks.
Rights, phase and disposal protection remain separate obligations. -/
namespace Ash.OneShot.SourceConsumingClauseAnnotations
open SourceContextualHints (Hints Requirement checkRequirements)
open SourceDependencyCapture (Scope)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceScheduledCapabilityAnnotations (DeclarationPolicy)

section
variable [declarations : DeclarationPolicy]

private def planDependencies {dependencies : SourceDependencyAnnotations.Dependencies}
    (_ : Plan dependencies) := dependencies

/-- Clause-local checking depends on the declared operation bounds, not the
code of the unknown captured continuation. The caller is generated from syntax;
independent pre-capture evidence supplies protection and retained validity. -/
def Body.BoundCheck {plan : Plan dependencies} (body : Body world owner plan)
    (resumeRequired closeRequired : List Requirement)
    (actions : Syntax.UsageTickets) (phases : OwnerPhaseTransitions.Phases)
    (receiving waiting : Scope) {frontHints : Hints frontScope} {front : Forest frontHints}
    (before : Interfaces world front) : Prop :=
  match body with
  | .resume =>
      (actions owner).any (fun rights => rights.resume) = true ∧ phases owner = .available ∧
      checkRequirements (frontScope.append (.spent owner waiting)) resumeRequired = true ∧
      before.check (.spent owner waiting) = true
  | .dispose =>
      (actions owner).any (fun rights => rights.dispose) = true ∧ phases owner = .available ∧
      checkRequirements (.running (frontScope.append (.spent owner waiting))) closeRequired = true ∧
      before.check (.spent owner waiting) = true
  | .sequence (after := next) required _ _ rest =>
      checkRequirements (.plain (planDependencies next) receiving) required = true ∧
      rest.BoundCheck resumeRequired closeRequired actions phases receiving waiting before
  | .choice first second =>
      first.BoundCheck resumeRequired closeRequired actions phases receiving waiting before ∧
      second.BoundCheck resumeRequired closeRequired actions phases receiving waiting before
  | .handler (effect := effect) (table := table) (families := families) (required := required) _ _ body =>
      checkRequirements receiving required = true ∧
      body.BoundCheck resumeRequired closeRequired actions phases (.handler effect table families receiving) waiting
        (.handler (effect := effect) (table := table) (families := families) (required := required) front before)
  | .cleanup (needs := needs) (callback := callback) required footprint declared body =>
      body.BoundCheck resumeRequired closeRequired actions phases
        (.cleanup needs (planDependencies callback) receiving) waiting
        (.cleanup (needs := needs) front required footprint declared before) ∧
      checkRequirements (.running receiving) required = true
  | .resource body => ∀ identity fresh,
      (body identity fresh).BoundCheck resumeRequired closeRequired actions phases (.cell identity receiving) waiting
        (.cell (identity := identity) (before.world_weaken (List.subset_append_left _ _)))

/-- The source-facing rule derives exact capture checks from original retained
checks and finite operation bounds. It assumes no successful future clause body
and reuses the established boundary transport and world-extension proofs. -/
theorem Body.check_from_contract {plan : Plan dependencies} (body : Body world owner plan)
    {frontHints : Hints frontScope} {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
    {inside : Interfaces world saved} {closing : Interfaces world saved.forClosing}
    {before : Interfaces world front} {after : Interfaces world tail}
    (checked : body.BoundCheck resumeRequired closeRequired actions phases receiving tailScope before)
    (resumeBound : (actions owner).any (fun rights => rights.resume) = true → inside.exposed ⊆ resumeRequired)
    (closeBound : (actions owner).any (fun rights => rights.dispose) = true → closing.exposed ⊆ closeRequired)
    (resumeReady : (actions owner).any (fun rights => rights.resume) = true → inside.check resumeOutside = true)
    (closeReady : (actions owner).any (fun rights => rights.dispose) = true → closing.check closeOutside = true)
    (disposal : (actions owner).any (fun rights => rights.dispose) = true →
      savedScope.held = false ∧ SourceDependencyCapture.checkClosing outward savedScope.shape [] [] = true)
    (tailReady : after.check .nil = true) :
    body.Check outward actions phases receiving inside closing before after := by
  induction body generalizing receiving frontScope with
  | resume =>
      exact ⟨checked.1, checked.2.1,
        inside.check_from_bound (resumeReady checked.1) (resumeBound checked.1) checked.2.2.1,
        checked.2.2.2, tailReady⟩
  | dispose =>
      exact ⟨checked.1, checked.2.1, (disposal checked.1).1, (disposal checked.1).2,
        closing.check_from_bound (closeReady checked.1) (closeBound checked.1) checked.2.2.1,
        checked.2.2.2, tailReady⟩
  | sequence required footprint declared rest ih =>
      exact ⟨checked.1, ih checked.2 resumeBound closeBound resumeReady closeReady disposal tailReady⟩
  | choice first second ihFirst ihSecond =>
      exact ⟨ihFirst checked.1 resumeBound closeBound resumeReady closeReady disposal tailReady,
        ihSecond checked.2 resumeBound closeBound resumeReady closeReady disposal tailReady⟩
  | handler bounds admitted body ih =>
      exact ⟨checked.1, ih checked.2 resumeBound closeBound resumeReady closeReady disposal tailReady⟩
  | cleanup required footprint declared body ih =>
      exact ⟨ih checked.1 resumeBound closeBound resumeReady closeReady disposal tailReady, checked.2⟩
  | resource body ih =>
      intro identity fresh
      apply ih identity fresh (checked identity fresh)
      · intro permission
        simpa only [Interfaces.exposed_world_weaken] using resumeBound permission
      · intro permission
        simpa only [Interfaces.exposed_world_weaken] using closeBound permission
      · intro permission
        simpa only [Interfaces.check_world_weaken] using resumeReady permission
      · intro permission
        simpa only [Interfaces.check_world_weaken] using closeReady permission
      · exact disposal
      · simpa only [Interfaces.check_world_weaken] using tailReady

end

namespace ContractExamples
open SourceScheduledClauseHandlers.Examples
  (code noActions bodies saved requesting waiting outerFamilies innerFamilies)
open SourceDependencyCapture.Examples (effectE effectF resumeTable)

def captured : Scope := .plain (.request effectF 0) (.handler effectE resumeTable outerFamilies .nil)
def waitingScope : Scope := .handler effectF resumeTable innerFamilies .nil

def retained : Interfaces [] requesting :=
  .plain saved [(effectF, 0)] .request .request (.handler .nil .nil)

/-- The contract states which operation the unknown continuation may expose.
The clause supplies it through its own newly installed F interpretation. -/
theorem clause_contract :
    (Examples.body 19).BoundCheck [(effectF, 0)] [] (noActions.insert 19 code.requiredActions)
      (OwnerPhaseTransitions.introduce OwnerPhaseTransitions.empty 19)
      (.live 19 captured waitingScope) waitingScope .nil :=
  ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩⟩⟩⟩⟩

/-- Only the original retained checks and its finite operation bound are used;
no checked future selected body or caller adaptation is an input. -/
theorem restored_check :
    (Examples.body 19).Check [] (noActions.insert 19 code.requiredActions)
      (OwnerPhaseTransitions.introduce OwnerPhaseTransitions.empty 19)
      (.live 19 captured waitingScope) retained .nil .nil
      (show Interfaces [] waiting from .handler .nil .nil) :=
  (Examples.body 19).check_from_contract (resumeOutside := waitingScope) (closeOutside := .nil)
    clause_contract (fun _ => List.Subset.refl _) (fun _ => List.Subset.refl _)
    (fun _ => rfl) (fun _ => rfl) (by intro impossible; cases impossible) rfl

/-- The source contract reaches the same existing one-shot scheduling kernel. -/
theorem restored_schedule :
    SourceScheduledChecks.Local [] (noActions.insert 19 code.requiredActions)
      (OwnerPhaseTransitions.introduce OwnerPhaseTransitions.empty 19) []
      (bodies 19) (.live (owner := 19) requesting waiting) :=
  (Examples.body 19).compile (SourceScheduledCapabilityAnnotations.recipeLaws [])
    retained .nil (.handler .nil .nil) restored_check

/-- Supplying the clause's own requests does not satisfy a missing operation
required by the captured continuation. -/
theorem missing_captured_operation :
    ¬ (Examples.body 19).BoundCheck [(.user 93 [], 0)] [] (noActions.insert 19 code.requiredActions)
      (OwnerPhaseTransitions.introduce OwnerPhaseTransitions.empty 19)
      (.live 19 captured waitingScope) waitingScope .nil := by
  intro checked
  have impossible : false = true := checked.2.2.2.2.2.2.1
  cases impossible

end ContractExamples

end Ash.OneShot.SourceConsumingClauseAnnotations

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.Body.check_from_contract

#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.ContractExamples.clause_contract
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.ContractExamples.restored_check
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.ContractExamples.restored_schedule
#print axioms Ash.OneShot.SourceConsumingClauseAnnotations.ContractExamples.missing_captured_operation
