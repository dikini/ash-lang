import SourceDependencyProjection
import SourceDependencyOwners

/-! Structural local checks for a source dependency tree at a specified
interpretation scope and owner phase. Sequencing exposes the pending suffix;
cleanup checks its body under an armed frame and its callback under running
protection. Disposing requests also bound captured pending code by its retained
owners. These are local contextual checks, not yet whole-source admission:
invocation checks the restored or scheduled source after owner consumption;
selected clause bodies still need checked declaration schemes, and control
transitions must preserve the combined source checks. -/
namespace Ash.OneShot.SourceDependencyChecks
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies Expression ValueSummary Environment)
open SourceDependencyCapture (CaptureGuard ResumeChecked DisposeChecked)
abbrev Receiving := SourceDependencyCapture.Scope
open OwnerPhaseTransitions (Phases)
open SourceDependencyProjection (project)
open RecursiveRequirements (Requirements evaluate)

mutual
/-- The source forms determine each local request's receiving scope. Clause
families are retained on handler frames; checking a selected family at capture
is a separate obligation. An invocation checks access and the retained source
in its projected transformed scope, with that owner marked consumed.
The projection removes spent markers only; runtime ownership is unchanged. -/
inductive Local (outward : List Instance) (actions : Syntax.UsageTickets) :
    Phases → List Nat → Dependencies → Receiving → Prop where
  | pure : Local outward actions phases world .pure scope
  | request (checked : CaptureGuard outward scope effect operation)
      (scheduled : ∀ captured tail contract modes,
        SourceDependencyCapture.select effect operation scope = some (.handler captured tail contract modes) →
        contract.dispose = true → Pending outward actions phases world
          (project captured.forClosing) (project (.running tail)))
      (ownerBound : ∀ captured tail contract modes,
        SourceDependencyCapture.select effect operation scope = some (.handler captured tail contract modes) →
        contract.dispose = true → SourceDependencyOwners.PendingWithin world
          (SourceDependencyOwners.owners captured) captured) :
      Local outward actions phases world (.request effect operation) scope
  | resume (checked : ResumeChecked actions phases owner scope after)
      (restored : Pending outward actions (OwnerPhaseTransitions.spend phases owner) world (project after) .nil) :
      Local outward actions phases world (.invoke ⟨owner, .resume⟩) scope
  | dispose (checked : DisposeChecked outward actions phases owner scope after)
      (scheduled : Pending outward actions (OwnerPhaseTransitions.spend phases owner) world (project after) .nil) :
      Local outward actions phases world (.invoke ⟨owner, .dispose⟩) scope
  | sequence (first : Local outward actions phases world before (.plain after scope))
      (second : Local outward actions phases world after scope) :
      Local outward actions phases world (.sequence before after) scope
  | choice (left : Local outward actions phases world first scope)
      (right : Local outward actions phases world second scope) :
      Local outward actions phases world (.choice first second) scope
  | handler (body : Local outward actions phases world dependencies (.handler effect table families scope)) :
      Local outward actions phases world (.handler effect table families dependencies) scope
  | cleanup (body : Local outward actions phases world dependencies (.cleanup needs callback scope))
      (completion : Local outward actions phases world callback (.running scope)) :
      Local outward actions phases world (.cleanup needs callback dependencies) scope
  | resource (body : ∀ identity, identity ∉ world →
      Local outward actions phases (world ++ [identity]) (family identity) (.cell identity scope)) :
      Local outward actions phases world (.resource family) scope

/-- Check the source already retained by a finite control forest. A dormant
capture is checked with its original receiving tail; resumption checks it again
with the actual caller inserted. No future transition or clause execution is a
premise. One-shot phases change at invocation rather than being silently reused. -/
inductive Pending (outward : List Instance) (actions : Syntax.UsageTickets) :
    Phases → List Nat → Receiving → Receiving → Prop where
  | nil : Pending outward actions phases world .nil outside
  | plain (code : Local outward actions phases world dependencies (rest.append outside))
      (tail : Pending outward actions phases world rest outside) :
      Pending outward actions phases world (.plain dependencies rest) outside
  | handler (tail : Pending outward actions phases world rest outside) :
      Pending outward actions phases world (.handler effect table families rest) outside
  | cell (tail : Pending outward actions phases world rest outside) :
      Pending outward actions phases world (.cell identity rest) outside
  | cleanup (callback : Local outward actions phases world dependencies (.running (rest.append outside)))
      (tail : Pending outward actions phases world rest outside) :
      Pending outward actions phases world (.cleanup needs dependencies rest) outside
  | running (tail : Pending outward actions phases world rest outside) :
      Pending outward actions phases world (.running rest) outside
  | live (saved : Pending outward actions phases world captured (rest.append outside))
      (tail : Pending outward actions phases world rest outside) :
      Pending outward actions phases world (.live owner captured rest) outside
  | spent (tail : Pending outward actions phases world rest outside) :
      Pending outward actions phases world (.spent owner rest) outside
end

/-- Actual values have no immediate operations or invocations. Their latent
function dependencies stay in their rich value type and are checked on use. -/
theorem Local.silent (silent : dependencies.Silent) : Local outward actions phases world dependencies scope := by
  induction silent generalizing scope with
  | pure => exact .pure
  | sequence first second ihFirst ihSecond => exact .sequence ihFirst ihSecond

theorem Local.sequence_iff : Local outward actions phases world (.sequence first second) scope ↔
    Local outward actions phases world first (.plain second scope) ∧ Local outward actions phases world second scope := by
  constructor
  · intro checked; cases checked with | sequence left right => exact ⟨left, right⟩
  · intro ⟨left, right⟩; exact .sequence left right

theorem Local.silent_prefix (silent : first.Silent) :
    Local outward actions phases world (.sequence first second) scope ↔ Local outward actions phases world second scope :=
  ⟨fun checked => (Local.sequence_iff.mp checked).2, fun checked => .sequence (.silent silent) checked⟩

/-- The arm and normal-completion scopes are different and both are checked.
A callback's own nested handler can still lie inside running protection. -/
theorem Local.cleanup_iff : Local outward actions phases world (.cleanup needs callback body) scope ↔
    Local outward actions phases world body (.cleanup needs callback scope) ∧
      Local outward actions phases world callback (.running scope) := by
  constructor
  · intro checked; cases checked with | cleanup body completion => exact ⟨body, completion⟩
  · intro ⟨body, completion⟩; exact .cleanup body completion

theorem Local.request_guard (checked : Local outward actions phases world (.request effect operation) scope) :
    SourceDependencyCapture.checkCapture outward scope effect operation = true := by
  cases checked with | request guarded scheduled ownerBound => exact SourceDependencyCapture.check_capture_iff.mpr guarded

/-- An admitted request checks the finite callback schedule selected by its
actual capture. No fresh continuation name or future clause execution occurs
in this premise. -/
theorem Local.request_schedule (checked : Local outward actions phases world (.request effect operation) scope)
    (found : SourceDependencyCapture.select effect operation scope = some (.handler captured tail contract modes))
    (disposes : contract.dispose = true) :
    Pending outward actions phases world (project captured.forClosing) (project (.running tail)) := by
  cases checked with | request guarded scheduled ownerBound => exact scheduled _ _ _ _ found disposes

theorem Local.request_owners (checked : Local outward actions phases world (.request effect operation) scope)
    (found : SourceDependencyCapture.select effect operation scope = some (.handler captured tail contract modes))
    (disposes : contract.dispose = true) :
    SourceDependencyOwners.PendingWithin world (SourceDependencyOwners.owners captured) captured := by
  cases checked with | request guarded scheduled ownerBound => exact ownerBound _ _ _ _ found disposes

/-- The nearest selected handler supplies the schedule. A different handler
or a different capture cannot discharge this source rule. -/
theorem Local.request_selected
    (found : SourceDependencyCapture.select effect operation scope = some (.handler captured tail contract modes))
    (guarded : SourceDependencyCapture.checkCapture outward scope effect operation = true)
    (scheduled : contract.dispose = true → Pending outward actions phases world
      (project captured.forClosing) (project (.running tail)))
    (ownerBound : contract.dispose = true → SourceDependencyOwners.PendingWithin world
      (SourceDependencyOwners.owners captured) captured) :
    Local outward actions phases world (.request effect operation) scope := by
  apply Local.request (SourceDependencyCapture.check_capture_iff.mp guarded)
  · intro actualCaptured actualTail actualContract actualModes selected disposes
    cases Option.some.inj (found.symm.trans selected)
    exact scheduled disposes
  · intro actualCaptured actualTail actualContract actualModes selected disposes
    cases Option.some.inj (found.symm.trans selected)
    exact ownerBound disposes

theorem scope_append_assoc (first second third : Receiving) :
    (first.append second).append third = first.append (second.append third) := by
  induction first <;> simp_all [SourceDependencyCapture.Scope.append]

/-- Split and join checked retained source at the same ordered interpretation
boundary. In particular, saved branches use the recomposed receiving tail. -/
theorem Pending.append_iff : Pending outward actions phases world (first.append second) outside ↔
    Pending outward actions phases world first (second.append outside) ∧
      Pending outward actions phases world second outside := by
  induction first generalizing outside with
  | nil => exact ⟨fun checked => ⟨.nil, checked⟩, fun ⟨_, checked⟩ => checked⟩
  | plain dependencies rest ih =>
      constructor
      · intro checked; cases checked with
        | plain code tail =>
            obtain ⟨inside, remaining⟩ := ih.mp tail
            exact ⟨.plain (by simpa only [scope_append_assoc] using code) inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | plain code tail =>
            exact .plain (by simpa only [scope_append_assoc] using code) (ih.mpr ⟨tail, remaining⟩)
  | cleanup needs dependencies rest ih =>
      constructor
      · intro checked; cases checked with
        | cleanup callback tail =>
            obtain ⟨inside, remaining⟩ := ih.mp tail
            exact ⟨.cleanup (by simpa only [scope_append_assoc] using callback) inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | cleanup callback tail =>
            exact .cleanup (by simpa only [scope_append_assoc] using callback) (ih.mpr ⟨tail, remaining⟩)
  | live owner captured rest ihCaptured ihRest =>
      constructor
      · intro checked; cases checked with
        | live saved tail =>
            obtain ⟨inside, remaining⟩ := ihRest.mp tail
            exact ⟨.live (by simpa only [scope_append_assoc] using saved) inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | live saved tail =>
            exact .live (by simpa only [scope_append_assoc] using saved) (ihRest.mpr ⟨tail, remaining⟩)
  | handler effect table families rest ih =>
      constructor
      · intro checked; cases checked with
        | handler tail => obtain ⟨inside, remaining⟩ := ih.mp tail; exact ⟨.handler inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | handler tail => exact .handler (ih.mpr ⟨tail, remaining⟩)
  | cell identity rest ih =>
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
  | spent owner rest ih =>
      constructor
      · intro checked; cases checked with
        | spent tail => obtain ⟨inside, remaining⟩ := ih.mp tail; exact ⟨.spent inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | spent tail => exact .spent (ih.mpr ⟨tail, remaining⟩)

/-- Capturing changes ownership of the saved forest while preserving the
receiving scopes of its retained source. Clause-body checking is additional. -/
theorem Pending.capture (checked : Pending outward actions phases world (captured.append tail) outside) :
    Pending outward actions phases world (.live owner captured tail) outside :=
  .live (Pending.append_iff.mp checked).1 (Pending.append_iff.mp checked).2

/-- The source invocation rule supplies checking of the actual restored
forest, after the invocation consumes its owner. It is stronger than access
permission alone and ranges over current retained syntax, not future traces. -/
theorem Local.resume_restored (checked : Local outward actions phases world (.invoke ⟨owner, .resume⟩) receiving) :
    ∃ after, SourceDependencyCapture.checkResume actions phases owner receiving = some after ∧
      Pending outward actions (OwnerPhaseTransitions.spend phases owner) world (project after) .nil := by
  cases checked with
  | resume access restored => exact ⟨_, SourceDependencyCapture.check_resume_iff.mpr access, restored⟩

theorem Local.dispose_scheduled (checked : Local outward actions phases world (.invoke ⟨owner, .dispose⟩) receiving) :
    ∃ after, SourceDependencyCapture.checkDispose outward actions phases owner receiving = some after ∧
      Pending outward actions (OwnerPhaseTransitions.spend phases owner) world (project after) .nil := by
  cases checked with
  | dispose access scheduled => exact ⟨_, SourceDependencyCapture.check_dispose_iff.mpr access, scheduled⟩

/-- Reuse the existing annotated source substitution theorem. It retains the
same dependency tree, so the contextual check requires no second substitution
induction or source-independent replacement annotation. -/
theorem substitution_preserves_local
    (source : Expression operations policy contracts world allowed lexical (environment.extend name input)
      code result demand requirements dependencies)
    (replacement : ValueSummary operations policy contracts world environment allowed value input)
    (closed : ClosedValue value)
    (checked : Local outward actions phases world dependencies receiving) :
    Expression operations policy contracts world allowed lexical environment (code.subst name value)
      result demand requirements dependencies ∧ Local outward actions phases world dependencies receiving :=
  ⟨SourceDependencyAnnotations.substitution source replacement closed, checked⟩

/-- Bind removes only a silent initializer. The exact remaining source,
contextual check and old requirement evaluation all follow existing lemmas. -/
theorem bind_preserves_local
    (source : Expression operations policy contracts world allowed lexical environment (.bind name value body)
      result demand requirements dependencies)
    (closed : ClosedValue value)
    (checked : Local outward actions phases world dependencies receiving) :
    ∃ (reduced : Requirements demand) (remaining : Dependencies),
      Expression operations policy contracts world allowed lexical environment (body.subst name value)
        result demand reduced remaining ∧ Local outward actions phases world remaining receiving ∧
      (∃ initial, dependencies = .sequence initial remaining ∧ initial.Silent) ∧
      ∀ store context before, evaluate store context before reduced = evaluate store context before requirements := by
  obtain ⟨reduced, remaining, next, ⟨initial, same, silent⟩, evaluation⟩ :=
    SourceDependencyAnnotations.bind_expression source closed
  subst dependencies
  exact ⟨reduced, remaining, next, (Local.silent_prefix silent).mp checked, ⟨initial, rfl, silent⟩, evaluation⟩

/-- Beta exposes the function's retained latent tree. Its function and
argument prefixes are silent; its lexical scope follows the existing rule. -/
theorem beta_preserves_local
    (source : Expression operations policy contracts world allowed lexical environment (.app (.lambda name body) value)
      result demand requirements dependencies)
    (closed : ClosedValue value)
    (checked : Local outward actions phases world dependencies receiving) :
    ∃ (reduced : Requirements demand) (remaining : Dependencies),
      Expression operations policy contracts world allowed .none environment (body.subst name value)
        result demand reduced remaining ∧ Local outward actions phases world remaining receiving ∧
      (∃ function argument, dependencies = .sequence function (.sequence argument remaining) ∧ function.Silent ∧ argument.Silent) ∧
      ∀ store context before, evaluate store context before reduced = evaluate store context before requirements := by
  obtain ⟨reduced, remaining, next, ⟨function, argument, same, functionSilent, argumentSilent⟩, evaluation⟩ :=
    SourceDependencyAnnotations.beta_expression source closed
  subst dependencies
  exact ⟨reduced, remaining, next,
    (Local.silent_prefix argumentSilent).mp ((Local.silent_prefix functionSilent).mp checked), ⟨function, argument, rfl, functionSilent, argumentSilent⟩, evaluation⟩


open RecursiveRequirements (Checked)

/-- Selecting either branch retains its contextual check and owner demand.
The existing choice decomposition supplies the checked row inclusion. -/
theorem branch_preserves_local
    (source : Expression operations policy contracts world allowed lexical environment (.branch (.boolean flag) yes no)
      result demand requirements dependencies)
    (checked : Local outward actions phases world dependencies receiving) :
    ∃ (remaining : List Nat) (reduced : Requirements remaining) (nextDependencies : Dependencies),
      Expression operations policy contracts world allowed lexical environment (if flag then yes else no)
        result remaining reduced nextDependencies ∧ Local outward actions phases world nextDependencies receiving ∧
      demand.Perm remaining ∧
      ∀ store context before row, Checked store context before requirements row →
        ∃ nextRow, Checked store context before reduced nextRow ∧ nextRow.Sublist row := by
  cases source with
  | branch condition yesSource noSource same =>
      cases condition with
      | boolean =>
          obtain ⟨_, branches⟩ := Local.sequence_iff.mp checked
          cases branches with
          | choice yesChecked noChecked =>
              cases flag with
              | false =>
                  refine ⟨_, _, _, noSource, noChecked, same, ?_⟩
                  intro store context before row checkedRow
                  have evaluated := RecursiveRequirements.checked_complete checkedRow
                  rw [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_empty,
                    RecursiveRecomposition.merge_empty_left] at evaluated
                  obtain ⟨firstRow, secondRow, left, right, rfl⟩ :=
                    RecursiveExpressions.choice_parts (RecursiveRequirements.evaluate_sound evaluated)
                  exact ⟨secondRow, right, List.sublist_append_right _ _⟩
              | true =>
                  refine ⟨_, _, _, yesSource, yesChecked, .refl _, ?_⟩
                  intro store context before row checkedRow
                  have evaluated := RecursiveRequirements.checked_complete checkedRow
                  rw [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_empty,
                    RecursiveRecomposition.merge_empty_left] at evaluated
                  obtain ⟨firstRow, secondRow, left, right, rfl⟩ :=
                    RecursiveExpressions.choice_parts (RecursiveRequirements.evaluate_sound evaluated)
                  exact ⟨firstRow, left, List.sublist_append_left _ _⟩

/-- A structurally checked source request supplies its capture guard at the
same receiving scope. At a ready operand, this is the actual capture site. -/
theorem perform_guard
    (source : Expression operations policy contracts world allowed lexical environment
      (.perform (Instantiation.freezeEffect effect) operation operand) result demand requirements dependencies)
    (checked : Local outward actions phases world dependencies receiving) :
    SourceDependencyCapture.checkCapture outward receiving effect operation = true := by
  generalize encoded : Instantiation.freezeEffect effect = syntaxEffect at source
  cases source with
  | perform known admitted operand formed =>
      cases freeze_effect_injective encoded
      exact Local.request_guard (Local.sequence_iff.mp checked).2

/-- The capture connection now derives the local guard from the current
structural source check. Source preservation must still establish that check
at every reached request, including inside selected clauses. -/
theorem capture_from_local
    (current : Expression operations policy contracts world allowed lexical environment
      (.perform (Instantiation.freezeEffect requested) operation operand) input currentDemand currentRequirements dependencies)
    (checked : Local record.annotation.closeEffects actions phases world dependencies receiving)
    (pending : SourceDependencyFrames.Segment operations policy contracts tables families actions world
      whole input output pendingDemand pendingRequirements records receiving incoming outgoing)
    (cut : HandlerCut requested whole capture tail handler)
    (known : lookup operation (tables handler) = some offered)
    (disposes : offered.dispose = true)
    (supported : Supported capture.erase (Admission.outsideResources capture.erase))
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending) :
    Nonempty (DeclaredClosingInvariant.Certificate operations.erase.ports world record capture) := by
  obtain ⟨answer, residual, capturedDemand, tailDemand, capturedRequirements, tailRequirements,
    capturedRecords, tailRecords, capturedScope, tailScope, certificate, saved, remaining, scopeSame, demandSame, recordsSame, owners⟩ :=
    SourceDependencyFrames.capture_certificate cut pending (perform_guard current checked) known disposes supported internal
  exact ⟨certificate⟩

namespace Examples
open SourceDependencyAnnotations.Examples

def receiving : Receiving := SourceDependencyCapture.Examples.handlerE (SourceDependencyCapture.Examples.handlerF .nil)

theorem cleanup_locally_checked : Local [effectF] (fun _ => none) OwnerPhaseTransitions.empty [] cleanupDependencies receiving := by
  apply Local.sequence .pure
  apply Local.cleanup
  · apply Local.sequence .pure
    apply Local.request_selected (found := rfl) (ownerBound := by intro possible; cases possible <;> repeat constructor)
    · decide
    · intro _
      apply Pending.cleanup
      · apply Local.sequence .pure
        apply Local.request_selected (found := rfl) (ownerBound := by intro possible; cases possible <;> repeat constructor)
        · decide
        · intro impossible; cases impossible
      · exact .nil
  · apply Local.sequence .pure
    apply Local.request_selected (found := rfl) (ownerBound := by intro possible; cases possible <;> repeat constructor)
    · decide
    · intro impossible; cases impossible

/-- These are actual source bind and beta steps in the existing example. Both
local checks and requirement evaluation are retained; capture execution and
selected clause checks are not claimed by this administrative-step example. -/
theorem higher_order_reduction_checked :
    ∃ first second : Requirements [],
      Expression operations policy contracts [] allowed .none Environment.empty (.app functionCode .unit)
        .unit [] first (.sequence .pure (.sequence .pure cleanupDependencies)) ∧
      Local [effectF] (fun _ => none) OwnerPhaseTransitions.empty []
        (.sequence .pure (.sequence .pure cleanupDependencies)) receiving ∧
      Expression operations policy contracts [] allowed .none Environment.empty cleanupBody
        .unit [] second cleanupDependencies ∧
      Local [effectF] (fun _ => none) OwnerPhaseTransitions.empty [] cleanupDependencies receiving ∧
      ∀ store context phases, evaluate store context phases second =
        evaluate store context phases (.sequence noRequirements invokedRequirements) := by
  have initially : Local [effectF] (fun _ => none) OwnerPhaseTransitions.empty [] boundDependencies receiving :=
    .sequence .pure (.sequence .pure (.sequence .pure cleanup_locally_checked))
  obtain ⟨first, afterBind, source, checked, ⟨initial, same, silent⟩, beforeCheck⟩ :=
    bind_preserves_local bound_function_retains_cleanup annotated_function_closed initially
  have bindSame : afterBind = .sequence .pure (.sequence .pure cleanupDependencies) :=
    (Dependencies.sequence.inj same).2.symm
  subst afterBind
  change Expression operations policy contracts [] allowed .none Environment.empty (.app functionCode .unit)
    .unit [] first (.sequence .pure (.sequence .pure cleanupDependencies)) at source
  have unitClosed : ClosedValue .unit := ⟨trivial, rfl, by intro _ member; cases member⟩
  obtain ⟨second, afterBeta, reduced, reducedCheck, ⟨function, argument, same, functionSilent, argumentSilent⟩, betaCheck⟩ :=
    beta_preserves_local source unitClosed checked
  have betaSame : afterBeta = cleanupDependencies := (Dependencies.sequence.inj (Dependencies.sequence.inj same).2).2.symm
  subst afterBeta
  change Expression operations policy contracts [] allowed .none Environment.empty cleanupBody .unit [] second cleanupDependencies at reduced
  exact ⟨first, second, source, checked, reduced, reducedCheck,
    fun store context phases => (betaCheck store context phases).trans (beforeCheck store context phases)⟩


def badReceiving : Receiving := SourceDependencyCapture.Examples.handlerF (SourceDependencyCapture.Examples.handlerE .nil)

/-- The same open source function is rejected when its caller puts the
callback's F handler inside the disposing E capture. -/
theorem bad_caller_rejected : ¬ Local [effectF] (fun _ => none) OwnerPhaseTransitions.empty [] boundDependencies badReceiving := by
  intro checked
  have cleanupChecked := (Local.sequence_iff.mp (Local.sequence_iff.mp (Local.sequence_iff.mp checked).2).2).2
  have armed := (Local.sequence_iff.mp cleanupChecked).2
  obtain ⟨body, completion⟩ := Local.cleanup_iff.mp armed
  have request := Local.request_guard (Local.sequence_iff.mp body).2
  have rejected := SourceDependencyCapture.Examples.removed_handler_rejected [effectF]
  change SourceDependencyCapture.checkCapture [effectF] SourceDependencyCapture.Examples.bad SourceDependencyCapture.Examples.effectE 0 = true at request
  rw [rejected] at request
  cases request

end Examples

open SourceDependencyCapture (OwnerSelection)
namespace CallerRechecking
open SourceDependencyCapture
open InvocationExamples (actions effectG savedCallback originalCaller)

def savedWork : Receiving := .plain (.request effectG 0) savedCallback
def beforeSafe : Receiving := .live 8 savedWork originalCaller
def beforeUnsafe : Receiving := Examples.handlerF beforeSafe

theorem safe_resume_checked : Local [SourceDependencyCapture.Examples.effectF] actions (OwnerPhaseTransitions.available [8]) []
    (.invoke ⟨8, .resume⟩) beforeSafe := by
  apply Local.resume (after := savedWork.append (.spent 8 originalCaller))
    (check_resume_iff.mp (show checkResume actions (OwnerPhaseTransitions.available [8]) 8 beforeSafe =
      some (savedWork.append (.spent 8 originalCaller)) from rfl))
  apply Pending.plain
  · apply Local.request_selected (found := rfl) (ownerBound := by intro possible; cases possible <;> repeat constructor)
    · decide
    · intro _
      apply Pending.cleanup
      · apply Local.sequence .pure
        apply Local.request_selected (found := rfl) (ownerBound := by intro possible; cases possible <;> repeat constructor)
        · decide
        · intro impossible; cases impossible
      · exact .nil
  · apply Pending.cleanup
    · apply Local.sequence .pure
      apply Local.request_selected (found := rfl) (ownerBound := by intro possible; cases possible <;> repeat constructor)
      · decide
      · intro impossible; cases impossible
    · exact .handler (.handler (.handler .nil))

/-- The stronger source invocation rule rejects the earlier interleaving:
the saved pending G request would discard its newly selected F interpretation.
This checks current retained dependency syntax rather than running the future. -/
theorem interleaved_resume_rejected : ¬ Local [SourceDependencyCapture.Examples.effectF] actions (OwnerPhaseTransitions.available [8]) []
    (.invoke ⟨8, .resume⟩) beforeUnsafe := by
  intro localCheck
  obtain ⟨after, computed, restored⟩ := Local.resume_restored localCheck
  have actual : checkResume actions (OwnerPhaseTransitions.available [8]) 8 beforeUnsafe =
      some (savedWork.append (Examples.handlerF (.spent 8 originalCaller))) := rfl
  have same := Option.some.inj (computed.symm.trans actual)
  subst after
  cases restored with
  | plain code tail =>
      have guarded := Local.request_guard code
      have rejected : checkCapture [SourceDependencyCapture.Examples.effectF]
          (project (savedCallback.append (Examples.handlerF (.spent 8 originalCaller)))) effectG 0 = false := by decide
      have impossible : false = true := rejected.symm.trans guarded
      cases impossible


def callbackOnly : Receiving := .cleanup [SourceDependencyCapture.Examples.effectF] SourceDependencyCapture.Examples.callback .nil
def disposalActions : Syntax.UsageTickets := fun _ => some ⟨false, true⟩
def disposeSafe : Receiving := .live 8 callbackOnly (Examples.handlerF .nil)
def badFinalizerHandler : Receiving :=
  .handler SourceDependencyCapture.Examples.effectF Examples.disposeTable Examples.disposeDependencies .nil

theorem safe_dispose_checked : Local [SourceDependencyCapture.Examples.effectF] disposalActions
    (OwnerPhaseTransitions.available [8]) [] (.invoke ⟨8, .dispose⟩) disposeSafe := by
  apply Local.dispose (after := callbackOnly.forClosing.append (.running (.spent 8 (Examples.handlerF .nil))))
    (check_dispose_iff.mp (show checkDispose [SourceDependencyCapture.Examples.effectF] disposalActions
      (OwnerPhaseTransitions.available [8]) 8 disposeSafe =
      some (callbackOnly.forClosing.append (.running (.spent 8 (Examples.handlerF .nil)))) from rfl))
  apply Pending.cleanup
  · apply Local.sequence .pure
    apply Local.request_selected (found := rfl) (ownerBound := by intro possible; cases possible <;> repeat constructor)
    · decide
    · intro impossible; cases impossible
  · exact .running (.handler .nil)

/-- A valid closing route does not license cancelling a running callback.
The scheduled-source premise checks the caller's selected capability too. -/
theorem cancelling_finalizer_handler_rejected : ¬ Local [SourceDependencyCapture.Examples.effectF] disposalActions
    (OwnerPhaseTransitions.available [8]) [] (.invoke ⟨8, .dispose⟩) (.live 8 callbackOnly badFinalizerHandler) := by
  intro localCheck
  obtain ⟨after, computed, scheduled⟩ := Local.dispose_scheduled localCheck
  have actual : checkDispose [SourceDependencyCapture.Examples.effectF] disposalActions
      (OwnerPhaseTransitions.available [8]) 8 (.live 8 callbackOnly badFinalizerHandler) =
      some (callbackOnly.forClosing.append (.running (.spent 8 badFinalizerHandler))) := rfl
  have same := Option.some.inj (computed.symm.trans actual)
  subst after
  cases scheduled with
  | cleanup callback tail =>
      have guarded := Local.request_guard (Local.sequence_iff.mp callback).2
      have rejected : checkCapture [SourceDependencyCapture.Examples.effectF]
          (project (.running (.running (.spent 8 badFinalizerHandler)))) SourceDependencyCapture.Examples.effectF 0 = false := by decide
      have impossible : false = true := rejected.symm.trans guarded
      cases impossible

/-- Closing routes alone accept this capture, but its surviving F handler
would cancel a running callback. Source admission must inspect the schedule. -/
def badRequestScope : Receiving := .cleanup [SourceDependencyCapture.Examples.effectF]
  SourceDependencyCapture.Examples.callback (Examples.handlerE badFinalizerHandler)

theorem route_guard_accepts_bad_schedule : checkCapture [SourceDependencyCapture.Examples.effectF]
    badRequestScope SourceDependencyCapture.Examples.effectE 0 = true := by decide

theorem request_rejects_bad_schedule : ¬ Local [SourceDependencyCapture.Examples.effectF] actions
    OwnerPhaseTransitions.empty [] (.request SourceDependencyCapture.Examples.effectE 0) badRequestScope := by
  intro checked
  have scheduled := Local.request_schedule checked rfl rfl
  cases scheduled with
  | cleanup callback tail =>
      have guarded := Local.request_guard (Local.sequence_iff.mp callback).2
      have rejected : checkCapture [SourceDependencyCapture.Examples.effectF]
          (.running (.running badFinalizerHandler)) SourceDependencyCapture.Examples.effectF 0 = false := by decide
      have impossible : false = true := rejected.symm.trans guarded
      cases impossible

end CallerRechecking

namespace OwnerBoundsExamples
open SourceDependencyOwners.Examples SourceDependencyCapture.Examples

theorem effect_guard_accepts_outside_owner :
    SourceDependencyCapture.checkCapture [] outside effectE 0 = true := by decide

theorem source_request_rejects_outside_owner :
    ¬ Local [] actions phases [] (.request effectE 0) outside := by
  intro checked
  exact outside_owner_rejected (Local.request_owners checked rfl rfl)

end OwnerBoundsExamples
end Ash.OneShot.SourceDependencyChecks

#print axioms Ash.OneShot.SourceDependencyChecks.Local.silent
#print axioms Ash.OneShot.SourceDependencyChecks.Local.sequence_iff
#print axioms Ash.OneShot.SourceDependencyChecks.Local.silent_prefix
#print axioms Ash.OneShot.SourceDependencyChecks.Local.cleanup_iff
#print axioms Ash.OneShot.SourceDependencyChecks.Local.request_guard
#print axioms Ash.OneShot.SourceDependencyChecks.Local.request_owners
#print axioms Ash.OneShot.SourceDependencyChecks.OwnerBoundsExamples.effect_guard_accepts_outside_owner
#print axioms Ash.OneShot.SourceDependencyChecks.OwnerBoundsExamples.source_request_rejects_outside_owner
#print axioms Ash.OneShot.SourceDependencyChecks.substitution_preserves_local
#print axioms Ash.OneShot.SourceDependencyChecks.bind_preserves_local
#print axioms Ash.OneShot.SourceDependencyChecks.beta_preserves_local
#print axioms Ash.OneShot.SourceDependencyChecks.Examples.cleanup_locally_checked
#print axioms Ash.OneShot.SourceDependencyChecks.Examples.higher_order_reduction_checked

#print axioms Ash.OneShot.SourceDependencyChecks.branch_preserves_local

#print axioms Ash.OneShot.SourceDependencyChecks.perform_guard

#print axioms Ash.OneShot.SourceDependencyChecks.capture_from_local

#print axioms Ash.OneShot.SourceDependencyChecks.Examples.bad_caller_rejected

#print axioms Ash.OneShot.SourceDependencyChecks.scope_append_assoc

#print axioms Ash.OneShot.SourceDependencyChecks.Pending.append_iff

#print axioms Ash.OneShot.SourceDependencyChecks.Pending.capture

#print axioms Ash.OneShot.SourceDependencyChecks.Local.resume_restored

#print axioms Ash.OneShot.SourceDependencyChecks.Local.dispose_scheduled

#print axioms Ash.OneShot.SourceDependencyChecks.CallerRechecking.safe_resume_checked

#print axioms Ash.OneShot.SourceDependencyChecks.CallerRechecking.interleaved_resume_rejected

#print axioms Ash.OneShot.SourceDependencyChecks.CallerRechecking.safe_dispose_checked

#print axioms Ash.OneShot.SourceDependencyChecks.CallerRechecking.cancelling_finalizer_handler_rejected

#print axioms Ash.OneShot.SourceDependencyChecks.Local.request_schedule
#print axioms Ash.OneShot.SourceDependencyChecks.Local.request_selected

#print axioms Ash.OneShot.SourceDependencyChecks.CallerRechecking.route_guard_accepts_bad_schedule
#print axioms Ash.OneShot.SourceDependencyChecks.CallerRechecking.request_rejects_bad_schedule


namespace Ash.OneShot.SourceDependencyChecks
open ScopedExpressions ScopedExecution
open SourceDependencyAnnotations (Dependencies)
open SourceDependencyCapture (Scope Realizes)

/-- Checks for abandoned scopes. Ordinary pending code will not execute.
    Callback checking remains a separate source judgment, instantiated by the
    caller; this traversal neither schedules callbacks nor proves their bodies.
    A nested live capture is unwound before its retirement marker. -/
inductive UnwindPending (check : Dependencies → Receiving → Prop) : Receiving → Receiving → Prop where
  | nil : UnwindPending check .nil outside
  | plain (tail : UnwindPending check rest outside) :
      UnwindPending check (.plain dependencies rest) outside
  | handler (tail : UnwindPending check rest outside) :
      UnwindPending check (.handler effect table families rest) outside
  | cell (tail : UnwindPending check rest outside) :
      UnwindPending check (.cell identity rest) outside
  | cleanup (callback : check dependencies (.running (rest.append outside)))
      (tail : UnwindPending check rest outside) :
      UnwindPending check (.cleanup needs dependencies rest) outside
  | running (tail : UnwindPending check rest outside) :
      UnwindPending check (.running rest) outside
  | live (saved : UnwindPending check captured (.running (rest.append outside)))
      (tail : UnwindPending check rest outside) :
      UnwindPending check (.live owner captured rest) outside
  | spent (tail : UnwindPending check rest outside) :
      UnwindPending check (.spent owner rest) outside

/-- Splitting an abandoned prefix retains each callback's exact receiving
    scope, including the retirement boundary for nested captures. -/
theorem UnwindPending.append_iff : UnwindPending check (first.append second) outside ↔
    UnwindPending check first (second.append outside) ∧
      UnwindPending check second outside := by
  induction first generalizing outside with
  | nil => exact ⟨fun checked => ⟨.nil, checked⟩, fun ⟨_, checked⟩ => checked⟩
  | plain dependencies rest ih =>
      constructor
      · intro checked; cases checked with
        | plain tail => obtain ⟨inside, remaining⟩ := ih.mp tail; exact ⟨.plain inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | plain tail => exact .plain (ih.mpr ⟨tail, remaining⟩)
  | cleanup needs dependencies rest ih =>
      constructor
      · intro checked; cases checked with
        | cleanup callback tail =>
            obtain ⟨inside, remaining⟩ := ih.mp tail
            exact ⟨.cleanup (by simpa only [scope_append_assoc] using callback) inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | cleanup callback tail =>
            exact .cleanup (by simpa only [scope_append_assoc] using callback) (ih.mpr ⟨tail, remaining⟩)
  | live owner captured rest ihCaptured ihRest =>
      constructor
      · intro checked; cases checked with
        | live saved tail =>
            obtain ⟨inside, remaining⟩ := ihRest.mp tail
            exact ⟨.live (by simpa only [scope_append_assoc] using saved) inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | live saved tail =>
            exact .live (by simpa only [scope_append_assoc] using saved) (ihRest.mpr ⟨tail, remaining⟩)
  | handler effect table families rest ih =>
      constructor
      · intro checked; cases checked with
        | handler tail => obtain ⟨inside, remaining⟩ := ih.mp tail; exact ⟨.handler inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | handler tail => exact .handler (ih.mpr ⟨tail, remaining⟩)
  | cell identity rest ih =>
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
  | spent owner rest ih =>
      constructor
      · intro checked; cases checked with
        | spent tail => obtain ⟨inside, remaining⟩ := ih.mp tail; exact ⟨.spent inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | spent tail => exact .spent (ih.mpr ⟨tail, remaining⟩)

/-- Actual local popping preserves retained callback checks. The runtime
    transition, rather than this source scope abstraction, determines which
    protected markers may be popped. -/
theorem UnwindPending.advance
    (step : LexicalUnwind.Advance before after discharged)
    (source : Realizes tables families scope before)
    (checked : UnwindPending check scope outside) :
    ∃ next, Realizes tables families next after ∧ UnwindPending check next outside := by
  cases step with
  | plain =>
      cases source with
      | push frame tail => cases frame; cases checked with
        | plain rest => exact ⟨_, tail, rest⟩
  | handler =>
      cases source with
      | push frame tail => cases frame; cases checked with
        | handler rest => exact ⟨_, tail, rest⟩
  | cell =>
      cases source with
      | push frame tail => cases frame; cases checked with
        | cell rest => exact ⟨_, tail, rest⟩
  | spent =>
      cases source with
      | spent tail => cases checked with
        | spent rest => exact ⟨_, tail, rest⟩
  | retire =>
      cases source with
      | push frame tail => cases frame; cases checked with
        | running rest => exact ⟨_, tail, rest⟩
  | live =>
      cases source with
      | live saved tail => cases checked with
        | live inside rest =>
            exact ⟨_, saved.append (.push .retiring tail),
              UnwindPending.append_iff.mpr ⟨inside, .running rest⟩⟩

/-- Cleanup entry extracts the exact callback check from the source frame.
    The waiting tail remains an abandoned prefix; the outside scope is not
    silently included among the scopes to be disposed. -/
theorem UnwindPending.start_cleanup
    (source : SourceDependencyFrames.LexicalSegment operations policy contracts tables families actions world
      (.push (.armed action) rest) input output demand requirements records dependencyScope incoming outgoing)
    (checked : UnwindPending check dependencyScope outside) :
    ∃ allowed latent dependencies, ∃ nextRequirements : RecursiveRequirements.Requirements demand,
      ∃ nextScope,
      SourceDependencyAnnotations.Expression operations policy contracts world allowed .none
        SourceDependencyAnnotations.Environment.empty (.app action.action .unit) .unit []
        (.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent)
        (.sequence .pure (.sequence .pure dependencies)) ∧
      SourceDependencyFrames.LexicalSegment operations policy contracts tables families actions world
        (.push (.unwinding action) rest) .unit output demand nextRequirements records nextScope allowed outgoing ∧
      check dependencies (nextScope.append outside) ∧ UnwindPending check nextScope outside := by
  obtain ⟨allowed, latent, dependencies, nextRequirements, nextScope, suffix,
    original, next, expression, segment⟩ := source.start_cleanup
  subst dependencyScope nextScope
  cases checked with
  | cleanup callback tail =>
      exact ⟨allowed, latent, dependencies, nextRequirements, _, expression, segment,
        callback, .running tail⟩

/-- After a callback returns, popping its actual unwinding marker preserves
    the checks for the remaining abandoned scopes. This does not assert that
    those checks are preserved by the callback's intervening evaluation. -/
theorem UnwindPending.finish_cleanup
    (source : Realizes tables families scope (.push (.unwinding action) rest))
    (checked : UnwindPending check scope outside) :
    ∃ next, Realizes tables families next rest ∧ UnwindPending check next outside := by
  cases source with
  | push frame tail => cases frame; cases checked with
    | running remaining => exact ⟨_, tail, remaining⟩

/-- Ordinary application adds only silent value prefixes to the callback's
    recorded dependencies. Reuse the existing structural sequencing proof. -/
theorem cleanup_application_checked
    (callback : Local outward actions phases world dependencies scope) :
    Local outward actions phases world (.sequence .pure (.sequence .pure dependencies)) scope :=
  Local.silent_prefix .pure |>.mpr (Local.silent_prefix .pure |>.mpr callback)

namespace LexicalExamples
/-- A callback may still use its enclosing resource during lexical unwinding. -/
theorem resource_callback_checked :
    UnwindPending (Local [] (fun _ => none) OwnerPhaseTransitions.empty [7])
      (.cleanup [.cell 7] (.request (.cell 7) 0) (.cell 7 .nil)) .nil := by
  apply UnwindPending.cleanup
  · apply Local.request
    · exact SourceDependencyCapture.check_capture_iff.mp (by decide)
    · intro captured tail contract modes selected
      cases selected
    · intro captured tail contract modes selected
      cases selected
  · exact .cell .nil

/-- Releasing the resource first loses a real callback requirement; an
    unchanged callback annotation cannot certify the shortened scope. -/
theorem released_resource_callback_rejected :
    ¬ UnwindPending (Local [] (fun _ => none) OwnerPhaseTransitions.empty [7])
      (.cleanup [.cell 7] (.request (.cell 7) 0) .nil) .nil := by
  intro checked
  cases checked with
  | cleanup callback tail =>
      have guarded := Local.request_guard callback
      cases guarded
end LexicalExamples

#print axioms Ash.OneShot.SourceDependencyChecks.LexicalExamples.resource_callback_checked
#print axioms Ash.OneShot.SourceDependencyChecks.LexicalExamples.released_resource_callback_rejected
#print axioms Ash.OneShot.SourceDependencyChecks.UnwindPending.start_cleanup
#print axioms Ash.OneShot.SourceDependencyChecks.UnwindPending.finish_cleanup
#print axioms Ash.OneShot.SourceDependencyChecks.cleanup_application_checked
#print axioms Ash.OneShot.SourceDependencyChecks.UnwindPending.append_iff
#print axioms Ash.OneShot.SourceDependencyChecks.UnwindPending.advance
end Ash.OneShot.SourceDependencyChecks


namespace Ash.OneShot.SourceDependencyChecks.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies)
open SourceDependencyCapture (OwnerCut ResumeChecked Realizes)
open OwnerPhaseTransitions (Phases spend)

/-- Capture checks the selected clause interface and protection mode. Disposal
    checks the retained callbacks at its actual caller, rather than extracting
    a schedule at capture. Clause-body admission remains separate. -/
inductive Capture (scope : Receiving) (effect : Instance) (operation : Nat) : Prop where
  | builtin (found : SourceDependencyCapture.select effect operation scope = some (.builtin identity)) :
      Capture scope effect operation
  | handler (found : SourceDependencyCapture.select effect operation scope = some (.handler captured tail contract modes))
      (permission : modeCheck contract.dispose captured.held = true)
      (row : contract.row captured.held = some footprint)
      (body : SourceDependencyCapture.modeDependencies captured.held modes = some family) :
      Capture scope effect operation

mutual
/-- Source dependencies checked against the actual lexical interpretation
    stack. Invocations inspect finite retained syntax after consuming the owner;
    no generated plan or future execution appears in the premises. -/
inductive Local (outward : List Instance) (actions : Syntax.UsageTickets) :
    Phases → List Nat → Dependencies → Receiving → Prop where
  | pure : Local outward actions phases world .pure scope
  | request (checked : Capture scope effect operation)
      (callbacks : ∀ captured tail contract modes,
        SourceDependencyCapture.select effect operation scope = some (.handler captured tail contract modes) →
        contract.dispose = true → Unwind outward actions phases world captured (.running tail))
      (ownerBound : ∀ captured tail contract modes,
        SourceDependencyCapture.select effect operation scope = some (.handler captured tail contract modes) →
        contract.dispose = true → SourceDependencyOwners.PendingWithin world
          (SourceDependencyOwners.owners captured) captured) :
      Local outward actions phases world (.request effect operation) scope
  | resume (checked : ResumeChecked actions phases owner scope after)
      (restored : Pending outward actions (spend phases owner) world after .nil) :
      Local outward actions phases world (.invoke ⟨owner, .resume⟩) scope
  | dispose (located : OwnerCut owner scope selected) (known : actions owner = some rights)
      (permission : rights.dispose = true) (available : phases owner = .available)
      (unprotected : selected.captured.held = false)
      (callbacks : Unwind outward actions (spend phases owner) world
        selected.captured (.running (selected.front.append (.spent owner selected.tail))))
      (waiting : Pending outward actions (spend phases owner) world
        (selected.front.append (.spent owner selected.tail)) .nil) :
      Local outward actions phases world (.invoke ⟨owner, .dispose⟩) scope
  | sequence (first : Local outward actions phases world before (.plain after scope))
      (second : Local outward actions phases world after scope) :
      Local outward actions phases world (.sequence before after) scope
  | choice (left : Local outward actions phases world first scope)
      (right : Local outward actions phases world second scope) :
      Local outward actions phases world (.choice first second) scope
  | handler (body : Local outward actions phases world dependencies (.handler effect table families scope)) :
      Local outward actions phases world (.handler effect table families dependencies) scope
  | cleanup (body : Local outward actions phases world dependencies (.cleanup needs callback scope))
      (completion : Local outward actions phases world callback (.running scope)) :
      Local outward actions phases world (.cleanup needs callback dependencies) scope
  | resource (body : ∀ identity, identity ∉ world →
      Local outward actions phases (world ++ [identity]) (family identity) (.cell identity scope)) :
      Local outward actions phases world (.resource family) scope

/-- Ordinary retained code and dormant captures remain checked. At disposal,
    UnwindPending checks only the abandoned prefix; this judgment checks the
    caller that will continue after the closing delimiter is removed. -/
inductive Pending (outward : List Instance) (actions : Syntax.UsageTickets) :
    Phases → List Nat → Receiving → Receiving → Prop where
  | nil : Pending outward actions phases world .nil outside
  | plain (code : Local outward actions phases world dependencies (rest.append outside))
      (tail : Pending outward actions phases world rest outside) :
      Pending outward actions phases world (.plain dependencies rest) outside
  | handler (tail : Pending outward actions phases world rest outside) :
      Pending outward actions phases world (.handler effect table families rest) outside
  | cell (tail : Pending outward actions phases world rest outside) :
      Pending outward actions phases world (.cell identity rest) outside
  | cleanup (callback : Local outward actions phases world dependencies (.running (rest.append outside)))
      (tail : Pending outward actions phases world rest outside) :
      Pending outward actions phases world (.cleanup needs dependencies rest) outside
  | running (tail : Pending outward actions phases world rest outside) :
      Pending outward actions phases world (.running rest) outside
  | live (saved : Pending outward actions phases world captured (rest.append outside))
      (tail : Pending outward actions phases world rest outside) :
      Pending outward actions phases world (.live owner captured rest) outside
  | spent (tail : Pending outward actions phases world rest outside) :
      Pending outward actions phases world (.spent owner rest) outside

/-- Abandoned scopes carry the same lexical traversal as UnwindPending.
    This mutual form permits callback checks at the consumed owner phase. -/
inductive Unwind (outward : List Instance) (actions : Syntax.UsageTickets) :
    Phases → List Nat → Receiving → Receiving → Prop where
  | nil : Unwind outward actions phases world .nil outside
  | plain (tail : Unwind outward actions phases world rest outside) :
      Unwind outward actions phases world (.plain dependencies rest) outside
  | handler (tail : Unwind outward actions phases world rest outside) :
      Unwind outward actions phases world (.handler effect table families rest) outside
  | cell (tail : Unwind outward actions phases world rest outside) :
      Unwind outward actions phases world (.cell identity rest) outside
  | cleanup (callback : Local outward actions phases world dependencies (.running (rest.append outside)))
      (tail : Unwind outward actions phases world rest outside) :
      Unwind outward actions phases world (.cleanup needs dependencies rest) outside
  | running (tail : Unwind outward actions phases world rest outside) :
      Unwind outward actions phases world (.running rest) outside
  | live (saved : Unwind outward actions phases world captured (.running (rest.append outside)))
      (tail : Unwind outward actions phases world rest outside) :
      Unwind outward actions phases world (.live owner captured rest) outside
  | spent (tail : Unwind outward actions phases world rest outside) :
      Unwind outward actions phases world (.spent owner rest) outside


end

/-- Reuse the generic lexical traversal proofs with this concrete callback
    judgment. The conversion preserves every callback and scope unchanged. -/
theorem Unwind.traversal
    (checked : Unwind outward actions phases world scope outside) :
    UnwindPending (Local outward actions phases world) scope outside := by
  induction scope generalizing outside with
  | nil => exact .nil
  | plain dependencies rest ih => cases checked with
      | plain tail => exact .plain (ih tail)
  | handler effect table families rest ih => cases checked with
      | handler tail => exact .handler (ih tail)
  | cell identity rest ih => cases checked with
      | cell tail => exact .cell (ih tail)
  | cleanup needs dependencies rest ih => cases checked with
      | cleanup callback tail => exact .cleanup callback (ih tail)
  | running rest ih => cases checked with
      | running tail => exact .running (ih tail)
  | live owner captured rest ihCaptured ihRest => cases checked with
      | live saved tail => exact .live (ihCaptured saved) (ihRest tail)
  | spent owner rest ih => cases checked with
      | spent tail => exact .spent (ih tail)

theorem Unwind.of_traversal
    (checked : UnwindPending (Local outward actions phases world) scope outside) :
    Unwind outward actions phases world scope outside := by
  induction scope generalizing outside with
  | nil => exact .nil
  | plain dependencies rest ih => cases checked with
      | plain tail => exact .plain (ih tail)
  | handler effect table families rest ih => cases checked with
      | handler tail => exact .handler (ih tail)
  | cell identity rest ih => cases checked with
      | cell tail => exact .cell (ih tail)
  | cleanup needs dependencies rest ih => cases checked with
      | cleanup callback tail => exact .cleanup callback (ih tail)
  | running rest ih => cases checked with
      | running tail => exact .running (ih tail)
  | live owner captured rest ihCaptured ihRest => cases checked with
      | live saved tail => exact .live (ihCaptured saved) (ihRest tail)
  | spent owner rest ih => cases checked with
      | spent tail => exact .spent (ih tail)

/-- All administrative unwind cases reuse the generic traversal theorem. -/
theorem Unwind.advance
    (step : LexicalUnwind.Advance before after discharged)
    (source : Realizes tables families scope before)
    (checked : Unwind outward actions phases world scope outside) :
    ∃ next, Realizes tables families next after ∧ Unwind outward actions phases world next outside := by
  obtain ⟨next, realized, remaining⟩ := checked.traversal.advance step source
  exact ⟨next, realized, Unwind.of_traversal remaining⟩

theorem Local.silent (silent : dependencies.Silent) : Local outward actions phases world dependencies scope := by
  induction silent generalizing scope with
  | pure => exact .pure
  | sequence first second ihFirst ihSecond => exact .sequence ihFirst ihSecond

theorem Local.sequence_iff : Local outward actions phases world (.sequence first second) scope ↔
    Local outward actions phases world first (.plain second scope) ∧ Local outward actions phases world second scope := by
  constructor
  · intro checked; cases checked with | sequence left right => exact ⟨left, right⟩
  · intro ⟨left, right⟩; exact .sequence left right

theorem Local.silent_prefix (silent : first.Silent) :
    Local outward actions phases world (.sequence first second) scope ↔ Local outward actions phases world second scope :=
  ⟨fun checked => (Local.sequence_iff.mp checked).2, fun checked => .sequence (.silent silent) checked⟩

/-- The arm and normal-completion scopes are different and both are checked.
A callback's own nested handler can still lie inside running protection. -/
theorem Local.cleanup_iff : Local outward actions phases world (.cleanup needs callback body) scope ↔
    Local outward actions phases world body (.cleanup needs callback scope) ∧
      Local outward actions phases world callback (.running scope) := by
  constructor
  · intro checked; cases checked with | cleanup body completion => exact ⟨body, completion⟩
  · intro ⟨body, completion⟩; exact .cleanup body completion

theorem Pending.append_iff : Pending outward actions phases world (first.append second) outside ↔
    Pending outward actions phases world first (second.append outside) ∧
      Pending outward actions phases world second outside := by
  induction first generalizing outside with
  | nil => exact ⟨fun checked => ⟨.nil, checked⟩, fun ⟨_, checked⟩ => checked⟩
  | plain dependencies rest ih =>
      constructor
      · intro checked; cases checked with
        | plain code tail =>
            obtain ⟨inside, remaining⟩ := ih.mp tail
            exact ⟨.plain (by simpa only [scope_append_assoc] using code) inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | plain code tail =>
            exact .plain (by simpa only [scope_append_assoc] using code) (ih.mpr ⟨tail, remaining⟩)
  | cleanup needs dependencies rest ih =>
      constructor
      · intro checked; cases checked with
        | cleanup callback tail =>
            obtain ⟨inside, remaining⟩ := ih.mp tail
            exact ⟨.cleanup (by simpa only [scope_append_assoc] using callback) inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | cleanup callback tail =>
            exact .cleanup (by simpa only [scope_append_assoc] using callback) (ih.mpr ⟨tail, remaining⟩)
  | live owner captured rest ihCaptured ihRest =>
      constructor
      · intro checked; cases checked with
        | live saved tail =>
            obtain ⟨inside, remaining⟩ := ihRest.mp tail
            exact ⟨.live (by simpa only [scope_append_assoc] using saved) inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | live saved tail =>
            exact .live (by simpa only [scope_append_assoc] using saved) (ihRest.mpr ⟨tail, remaining⟩)
  | handler effect table families rest ih =>
      constructor
      · intro checked; cases checked with
        | handler tail => obtain ⟨inside, remaining⟩ := ih.mp tail; exact ⟨.handler inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | handler tail => exact .handler (ih.mpr ⟨tail, remaining⟩)
  | cell identity rest ih =>
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
  | spent owner rest ih =>
      constructor
      · intro checked; cases checked with
        | spent tail => obtain ⟨inside, remaining⟩ := ih.mp tail; exact ⟨.spent inside, remaining⟩
      · intro ⟨inside, remaining⟩; cases inside with
        | spent tail => exact .spent (ih.mpr ⟨tail, remaining⟩)

/-- Capturing changes ownership of the saved forest while preserving the
receiving scopes of its retained source. Clause-body checking is additional. -/
theorem Pending.capture (checked : Pending outward actions phases world (captured.append tail) outside) :
    Pending outward actions phases world (.live owner captured tail) outside :=
  .live (Pending.append_iff.mp checked).1 (Pending.append_iff.mp checked).2

/-- Source lookup selects the same runtime capture and caller. The resulting
    lexical unwind retains both their annotations, with checks in the consumed
    phase and with the actual closing delimiter as callback protection. -/
theorem Local.discard_step
    (source : Realizes tables families dependencyScope stack)
    (checked : Local outward actions phases world (.invoke ⟨owner, .dispose⟩) dependencyScope)
    (resolved : caller.resolve binder = some owner) :
    ∃ captured waiting capturedScope waitingScope,
      LexicalUnwind.Transition (.eval ⟨.discard binder, caller, stack⟩)
        (.unwind caller (captured.append (.push (.closing identity caller) waiting)))
        [.close identity] [.ticket owner] ∧
      Realizes tables families capturedScope captured ∧
      Realizes tables families waitingScope waiting ∧
      UnwindPending (Local outward actions (spend phases owner) world)
        capturedScope (.running waitingScope) ∧
      Pending outward actions (spend phases owner) world waitingScope .nil := by
  cases checked with
  | dispose located known permission available unprotected callbacks waiting =>
      obtain ⟨front, captured, tail, input, answer, savedScope, same, frontSource, saved, outside⟩ :=
        source.find_owner located.lookup
      subst stack
      exact ⟨_, _, _, _,
        .discard binder owner identity caller savedScope input answer front captured tail resolved
          (saved.held ▸ unprotected),
        saved, frontSource.append (.spent outside), callbacks.traversal, waiting⟩

/-- Resumption retains ordinary pending source at the actual recomposed
    caller. Reuse the existing lookup and runtime-step correspondence. -/
theorem Local.resume_step
    (source : Realizes tables families dependencyScope stack)
    (checked : Local outward actions phases world (.invoke ⟨owner, .resume⟩) dependencyScope)
    (resolved : caller.resolve binder = some owner) (closed : ClosedValue value) :
    ∃ afterScope afterStack,
      RawStep ⟨.resume binder value, caller, stack⟩ ⟨value, caller, afterStack⟩ [] [.ticket owner] ∧
      Realizes tables families afterScope afterStack ∧
      Pending outward actions (spend phases owner) world afterScope .nil := by
  cases checked with
  | resume access restored =>
      obtain ⟨afterStack, step, realized⟩ := SourceDependencyCapture.checked_resume_step source
        (SourceDependencyCapture.check_resume_iff.mpr access) resolved closed
      exact ⟨_, afterStack, step, realized, restored⟩

/-- A consumed continuation cannot acquire another disposal derivation. -/
theorem Local.consumed_dispose_rejected :
    ¬ Local outward actions (spend phases owner) world (.invoke ⟨owner, .dispose⟩) scope := by
  intro checked
  cases checked with
  | dispose located known permission available =>
      simp only [OwnerPhaseTransitions.spend_self] at available
      cases available

/-- The same independent one-shot phase check applies to resumption. -/
theorem Local.consumed_resume_rejected :
    ¬ Local outward actions (spend phases owner) world (.invoke ⟨owner, .resume⟩) scope := by
  intro checked
  cases checked with
  | resume access restored => cases access with
    | checked located known permission available =>
        simp only [OwnerPhaseTransitions.spend_self] at available
        cases available

theorem Unwind.start_cleanup
    (source : SourceDependencyFrames.LexicalSegment operations policy contracts tables families actions world
      (.push (.armed action) rest) input output demand requirements records dependencyScope incoming outgoing)
    (checked : Unwind outward actions phases world dependencyScope outside) :
    ∃ allowed latent dependencies, ∃ nextRequirements : RecursiveRequirements.Requirements demand,
      ∃ nextScope,
      SourceDependencyAnnotations.Expression operations policy contracts world allowed .none
        SourceDependencyAnnotations.Environment.empty (.app action.action .unit) .unit []
        (.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent)
        (.sequence .pure (.sequence .pure dependencies)) ∧
      SourceDependencyFrames.LexicalSegment operations policy contracts tables families actions world
        (.push (.unwinding action) rest) .unit output demand nextRequirements records nextScope allowed outgoing ∧
      Local outward actions phases world (.sequence .pure (.sequence .pure dependencies))
        (nextScope.append outside) ∧ Unwind outward actions phases world nextScope outside := by
  obtain ⟨allowed, latent, dependencies, nextRequirements, nextScope,
    expression, segment, callback, remaining⟩ := checked.traversal.start_cleanup source
  exact ⟨allowed, latent, dependencies, nextRequirements, nextScope, expression, segment,
    .sequence .pure (.sequence .pure callback), Unwind.of_traversal remaining⟩

/-- Callback return reuses the actual-marker traversal proof. -/
theorem Unwind.finish_cleanup
    (source : Realizes tables families scope (.push (.unwinding action) rest))
    (checked : Unwind outward actions phases world scope outside) :
    ∃ next, Realizes tables families next rest ∧ Unwind outward actions phases world next outside := by
  obtain ⟨next, realized, remaining⟩ := checked.traversal.finish_cleanup source
  exact ⟨next, realized, Unwind.of_traversal remaining⟩

namespace Examples
open SourceDependencyCapture.Examples
/-- Lexical disposal retains the handler needed by cleanup inside the capture.
    The old schedule-based guard rejected this shape after removing that handler. -/
theorem retained_cleanup_handler_dispose :
    Local [] (fun _ => some ⟨false, true⟩) (OwnerPhaseTransitions.available [8]) []
      (.invoke ⟨8, .dispose⟩) (.live 8 (.cleanup [effectF] callback (handlerF .nil)) .nil) := by
  apply Local.dispose OwnerCut.hit rfl rfl (by decide) rfl
  · apply Unwind.cleanup
    · apply Local.sequence .pure
      apply Local.request (.handler (found := rfl) rfl rfl rfl)
      all_goals
        intro captured tail contract modes found possible
        cases found
        cases possible
    · exact .handler .nil
  · exact .spent .nil

/-- A disposal-capable interpretation still cannot cancel a running callback.
    Keeping lexical handlers does not weaken the protection guard. -/
theorem cancelling_callback_rejected :
    ¬ Local [] actions phases world (.request effectE 0) (.running (handlerE .nil)) := by
  intro checked
  cases checked with
  | request guarded callbacks owners => cases guarded with
    | builtin found => cases found
    | handler found permission row body => cases found; cases permission
end Examples

#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.Local.silent
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.Local.sequence_iff
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.Local.silent_prefix
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.Local.cleanup_iff
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.Pending.append_iff
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.Pending.capture
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.Unwind.start_cleanup
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.Unwind.finish_cleanup
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.Unwind.of_traversal
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.Unwind.advance
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.Local.resume_step
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.Local.consumed_dispose_rejected
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.Local.consumed_resume_rejected
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.Examples.retained_cleanup_handler_dispose
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.Examples.cancelling_callback_rejected
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.Unwind.traversal
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.Local.discard_step
end Ash.OneShot.SourceDependencyChecks.Lexical


namespace Ash.OneShot.SourceDependencyChecks.Lexical
/-- Extending the historical resource world preserves the same lexical checks.
    Fresh-body families are restricted to identities still fresh in the larger world. -/
theorem Local.world_weaken
    (checked : Local outward actions phases world dependencies scope) (larger : world ⊆ nextWorld) :
    Local outward actions phases nextWorld dependencies scope := by
  refine (Local.rec
    (motive_1 := fun phases world dependencies scope _ => ∀ {nextWorld}, world ⊆ nextWorld →
      Local outward actions phases nextWorld dependencies scope)
    (motive_2 := fun phases world scope outside _ => ∀ {nextWorld}, world ⊆ nextWorld →
      Pending outward actions phases nextWorld scope outside)
    (motive_3 := fun phases world scope outside _ => ∀ {nextWorld}, world ⊆ nextWorld →
      Unwind outward actions phases nextWorld scope outside)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (t := checked)) larger
  · intros; exact .pure
  · intros
    rename_i guard callbacks bound ihCallbacks nextWorld larger
    exact .request guard
      (fun captured tail contract modes selected disposes => ihCallbacks captured tail contract modes selected disposes larger)
      (fun captured tail contract modes selected disposes =>
        (bound captured tail contract modes selected disposes).world_weaken larger)
  · intros
    rename_i access restored ih nextWorld larger
    exact .resume access (ih larger)
  · intros
    rename_i located known permission available unprotected callbacks waiting ihCallbacks ihWaiting nextWorld larger
    exact .dispose located known permission available unprotected (ihCallbacks larger) (ihWaiting larger)
  · intros
    rename_i first second ihFirst ihSecond nextWorld larger
    exact .sequence (ihFirst larger) (ihSecond larger)
  · intros
    rename_i first second ihFirst ihSecond nextWorld larger
    exact .choice (ihFirst larger) (ihSecond larger)
  · intros
    rename_i body ih nextWorld larger
    exact .handler (ih larger)
  · intros
    rename_i body callback ihBody ihCallback nextWorld larger
    exact .cleanup (ihBody larger) (ihCallback larger)
  · intros
    rename_i body ih nextWorld larger
    exact .resource (fun identity fresh => ih identity (fun member => fresh (larger member))
      (ScopedExpressions.append_subset larger (List.Subset.refl _)))
  · intros; exact .nil
  · intros
    rename_i first second ihFirst ihSecond nextWorld larger
    exact .plain (ihFirst larger) (ihSecond larger)
  · intros
    rename_i tail ih nextWorld larger
    exact .handler (ih larger)
  · intros
    rename_i tail ih nextWorld larger
    exact .cell (ih larger)
  · intros
    rename_i first second ihFirst ihSecond nextWorld larger
    exact .cleanup (ihFirst larger) (ihSecond larger)
  · intros
    rename_i tail ih nextWorld larger
    exact .running (ih larger)
  · intros
    rename_i first second ihFirst ihSecond nextWorld larger
    exact .live (ihFirst larger) (ihSecond larger)
  · intros
    rename_i tail ih nextWorld larger
    exact .spent (ih larger)
  · intros; exact .nil
  · intros
    rename_i tail ih nextWorld larger
    exact .plain (ih larger)
  · intros
    rename_i tail ih nextWorld larger
    exact .handler (ih larger)
  · intros
    rename_i tail ih nextWorld larger
    exact .cell (ih larger)
  · intros
    rename_i first second ihFirst ihSecond nextWorld larger
    exact .cleanup (ihFirst larger) (ihSecond larger)
  · intros
    rename_i tail ih nextWorld larger
    exact .running (ih larger)
  · intros
    rename_i first second ihFirst ihSecond nextWorld larger
    exact .live (ihFirst larger) (ihSecond larger)
  · intros
    rename_i tail ih nextWorld larger
    exact .spent (ih larger)

/-- Retained ordinary code reuses local world transport at its exact suffix. -/
theorem Pending.world_weaken
    (checked : Pending outward actions phases world scope outside) (larger : world ⊆ nextWorld) :
    Pending outward actions phases nextWorld scope outside := by
  induction scope generalizing outside with
  | nil => exact .nil
  | plain dependencies rest ih => cases checked with
    | plain code tail => exact .plain (code.world_weaken larger) (ih tail)
  | handler effect table families rest ih => cases checked with | handler tail => exact .handler (ih tail)
  | cell identity rest ih => cases checked with | cell tail => exact .cell (ih tail)
  | cleanup needs dependencies rest ih => cases checked with
    | cleanup callback tail => exact .cleanup (callback.world_weaken larger) (ih tail)
  | running rest ih => cases checked with | running tail => exact .running (ih tail)
  | live owner captured rest ihCaptured ihRest => cases checked with
    | live saved tail => exact .live (ihCaptured saved) (ihRest tail)
  | spent owner rest ih => cases checked with | spent tail => exact .spent (ih tail)

theorem Unwind.world_weaken
    (checked : Unwind outward actions phases world scope outside) (larger : world ⊆ nextWorld) :
    Unwind outward actions phases nextWorld scope outside := by
  induction scope generalizing outside with
  | nil => exact .nil
  | plain dependencies rest ih => cases checked with | plain tail => exact .plain (ih tail)
  | handler effect table families rest ih => cases checked with | handler tail => exact .handler (ih tail)
  | cell identity rest ih => cases checked with | cell tail => exact .cell (ih tail)
  | cleanup needs dependencies rest ih => cases checked with
    | cleanup callback tail => exact .cleanup (callback.world_weaken larger) (ih tail)
  | running rest ih => cases checked with | running tail => exact .running (ih tail)
  | live owner captured rest ihCaptured ihRest => cases checked with
    | live saved tail => exact .live (ihCaptured saved) (ihRest tail)
  | spent owner rest ih => cases checked with | spent tail => exact .spent (ih tail)

#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.Local.world_weaken
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.Pending.world_weaken
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.Unwind.world_weaken
end Ash.OneShot.SourceDependencyChecks.Lexical


namespace Ash.OneShot.SourceDependencyChecks.Lexical.Examples
open SourceDependencyCapture.Examples
open SourceDependencyChecks.Lexical
/-- A disposing request keeps the captured interpretation needed by cleanup.
    The added callback premise is lexical and accepts the former planner gap. -/
theorem disposing_request_retains_cleanup_handler :
    Local [] (fun _ => none) OwnerPhaseTransitions.empty [] (.request effectE 0) bad := by
  apply Local.request (.handler (found := rfl) rfl rfl rfl)
  · intro captured tail contract modes selected disposes
    cases selected
    apply Unwind.cleanup
    · apply Local.sequence .pure
      apply Local.request (.handler (found := rfl) rfl rfl rfl)
      all_goals
        intro captured tail contract modes selected disposes
        cases selected
        cases disposes
    · exact .handler (.handler .nil)
  · intro captured tail contract modes selected disposes
    cases selected
    exact .cleanup (.handler (.handler .nil))
end Ash.OneShot.SourceDependencyChecks.Lexical.Examples

#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.Examples.disposing_request_retains_cleanup_handler


namespace Ash.OneShot.SourceDependencyChecks.Lexical
theorem Local.request_guard (checked : Local outward actions phases world (.request effect operation) scope) :
    Capture scope effect operation := by
  cases checked with | request guarded callbacks bounded => exact guarded
end Ash.OneShot.SourceDependencyChecks.Lexical

#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.Local.request_guard


namespace Ash.OneShot.SourceDependencyChecks.Lexical
open ScopedExpressions ProtectionContracts SourceDependencyCapture

/-- A disposing clause cannot abandon a protected capture. This uses only
    the lexical capture rule, not the legacy plan-routing check. -/
theorem Capture.disposing_unprotected
    (checked : Capture scope effect operation)
    (found : select effect operation scope = some (.handler captured tail contract modes))
    (disposes : contract.dispose = true) : captured.held = false := by
  cases checked with
  | builtin actual => rw [found] at actual; cases Option.some.inj actual
  | handler actual permission row body =>
      cases Option.some.inj (found.symm.trans actual)
      cases held : captured.held with
      | false => rfl
      | true => simp [modeCheck, disposes, held] at permission

end Ash.OneShot.SourceDependencyChecks.Lexical

#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.Capture.disposing_unprotected


namespace Ash.OneShot.SourceDependencyChecks.Lexical
open ScopedExpressions ScopedExecution
open SourceDependencyAnnotations (Dependencies)
open SourceDependencyCapture (Scope Realizes)
open LexicalUnwind (UseMode)

/-- Local checks for a frame at its actual entry and exit usage modes. The
mode transition is determined by the runtime marker, independently of effects. -/
inductive ModeFrame (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases) (world : List Nat)
    (tables : CallableProtectionFrames.Tables) (families : SourceDependencyCapture.Families)
    (outside : SourceDependencyCapture.Scope) :
    ExecFrame → (SourceDependencyCapture.Scope → SourceDependencyCapture.Scope) → UseMode → UseMode → Prop where
  | plain (code : Local outward actions phases world dependencies outside) :
      ModeFrame outward actions phases world tables families outside (.plain data) (.plain dependencies) .ordinary .ordinary
  | skipped : ModeFrame outward actions phases world tables families outside (.plain data) (.plain dependencies) .unwind .unwind
  | handler : ModeFrame outward actions phases world tables families outside (.handler data)
      (.handler data.effectInst (tables data) (families data)) mode mode
  | cell : ModeFrame outward actions phases world tables families outside (.cell identity payload scope answer) (.cell identity) mode mode
  | armed (callback : Local outward actions phases world dependencies (.running outside)) :
      ModeFrame outward actions phases world tables families outside (.armed action) (.cleanup action.requests dependencies) mode mode
  | running : ModeFrame outward actions phases world tables families outside (.running action saved closed) .running .ordinary .ordinary
  | unwinding : ModeFrame outward actions phases world tables families outside (.unwinding action) .running .ordinary .unwind
  | closing : ModeFrame outward actions phases world tables families outside (.closing identity scope) .running mode .ordinary
  | retiring : ModeFrame outward actions phases world tables families outside (.retiring owner) .running mode mode

/-- Actual scopes carry checks only for code executed in their current mode.
A live capture opened during unwinding is checked behind its retirement marker. -/
inductive ModePending (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases) (world : List Nat)
    (tables : CallableProtectionFrames.Tables) (families : SourceDependencyCapture.Families) :
    Stack → SourceDependencyCapture.Scope → SourceDependencyCapture.Scope → UseMode → UseMode → Prop where
  | nil : ModePending outward actions phases world tables families .nil .nil outside mode mode
  | push (frame : ModeFrame outward actions phases world tables families (restScope.append outside) entry layer before middle)
      (tail : ModePending outward actions phases world tables families rest restScope outside middle after) :
      ModePending outward actions phases world tables families (.push entry rest) (layer restScope) outside before after
  | live (saved : ModePending outward actions phases world tables families captured capturedScope (restScope.append outside) .ordinary middle)
      (tail : ModePending outward actions phases world tables families rest restScope outside middle after) :
      ModePending outward actions phases world tables families (.live owner input answer captured caller rest)
        (.live owner capturedScope restScope) outside .ordinary after
  | opening (saved : ModePending outward actions phases world tables families captured capturedScope (.running (restScope.append outside)) .unwind .unwind)
      (tail : ModePending outward actions phases world tables families rest restScope outside .unwind after) :
      ModePending outward actions phases world tables families (.live owner input answer captured caller rest)
        (.live owner capturedScope restScope) outside .unwind after
  | spent (tail : ModePending outward actions phases world tables families rest restScope outside before after) :
      ModePending outward actions phases world tables families (.spent owner answer caller rest)
        (.spent owner restScope) outside before after

theorem ModeFrame.realizes
    (checked : ModeFrame outward actions phases world tables families outside entry layer before after) :
    SourceDependencyCapture.Frame tables families layer entry := by
  cases checked with
  | plain | skipped => exact .plain
  | handler => exact .handler
  | cell => exact .cell
  | armed => exact .cleanup
  | running => exact .running
  | unwinding => exact .unwinding
  | closing => exact .closing
  | retiring => exact .retiring

theorem ModePending.realizes
    (checked : ModePending outward actions phases world tables families stack scope outside before after) :
    Realizes tables families scope stack := by
  induction checked with
  | nil => exact .nil
  | push frame tail ih => exact .push frame.realizes ih
  | live saved tail ihSaved ihTail | opening saved tail ihSaved ihTail => exact .live ihSaved ihTail
  | spent tail ih => exact .spent ih

/-- Recomposition uses the actual exit mode of the first fragment. Scope
association changes no request's receiving interpretations. -/
theorem ModePending.append
    (first : ModePending outward actions phases world tables families a firstScope (secondScope.append outside) before middle)
    (second : ModePending outward actions phases world tables families b secondScope outside middle after) :
    ModePending outward actions phases world tables families (a.append b) (firstScope.append secondScope) outside before after := by
  induction a generalizing firstScope before middle with
  | nil => cases first; exact second
  | push entry rest ih => cases first with
      | push frame tail =>
          rw [Stack.append, frame.realizes.append]
          exact .push (by simpa only [scope_append_assoc] using frame) (ih tail second)
  | live owner input answer saved caller rest ihSaved ihRest => cases first with
      | live inside tail =>
          exact .live (by simpa only [scope_append_assoc] using inside) (ihRest tail second)
      | opening inside tail =>
          exact .opening (by simpa only [scope_append_assoc] using inside) (ihRest tail second)
  | spent owner answer caller rest ih => cases first with
      | spent tail => exact .spent (ih tail second)

/-- The existing runtime return-mode function agrees with the structural
code checks, including transitions into and out of abandonment. -/
theorem ModePending.return_mode
    (checked : ModePending outward actions phases world tables families stack scope outside before after) :
    LexicalUnwind.returnMode stack before = after := by
  induction checked with
  | nil => rfl
  | push frame tail ih => cases frame <;> exact ih
  | live saved tail ihSaved ihTail | opening saved tail ihSaved ihTail =>
      simpa only [LexicalUnwind.returnMode, ihSaved] using ihTail
  | spent tail ih => exact ih

/-- Administrative unwinding retains the pending checks at the actual next
scope. Phase restriction is the separate one-shot capability obligation. -/
theorem ModePending.advance
    (step : LexicalUnwind.Advance before after discharged)
    (checked : ModePending outward actions phases world tables families before scope outside .unwind finalMode) :
    ModePending outward actions phases world tables families after scope.afterUnwind outside .unwind finalMode := by
  cases step with
  | plain | handler | cell | retire => cases checked with
      | push frame tail => cases frame <;> exact tail
  | spent => cases checked with | spent tail => exact tail
  | live => cases checked with
      | opening saved tail => exact saved.append (.push .retiring tail)
/-- Split checks at an actual stack boundary, retaining the mode exposed by
that boundary and the original source scopes. -/
theorem ModePending.split
    (checked : ModePending outward actions phases world tables families (first.append second) scope outside before after) :
    ∃ (middle : UseMode) (firstScope secondScope : SourceDependencyCapture.Scope),
      scope = firstScope.append secondScope ∧
      ModePending outward actions phases world tables families first firstScope (secondScope.append outside) before middle ∧
      ModePending outward actions phases world tables families second secondScope outside middle after := by
  induction first generalizing scope before after with
  | nil => exact ⟨before, .nil, scope, rfl, .nil, checked⟩
  | push entry rest ih => cases checked with
      | push frame tail =>
          obtain ⟨middle, firstScope, secondScope, same, inside, rest⟩ := ih tail
          subst same
          exact ⟨middle, _, secondScope, frame.realizes.append.symm,
            .push (by simpa only [scope_append_assoc] using frame) inside, rest⟩
  | live owner input answer saved caller rest ihSaved ihRest => cases checked with
      | live saved tail =>
          obtain ⟨middle, firstScope, secondScope, same, inside, rest⟩ := ihRest tail
          subst same
          exact ⟨middle, _, secondScope, rfl,
            .live (by simpa only [scope_append_assoc] using saved) inside, rest⟩
      | opening saved tail =>
          obtain ⟨middle, firstScope, secondScope, same, inside, rest⟩ := ihRest tail
          subst same
          exact ⟨middle, _, secondScope, rfl,
            .opening (by simpa only [scope_append_assoc] using saved) inside, rest⟩
  | spent owner answer caller rest ih => cases checked with
      | spent tail =>
          obtain ⟨middle, firstScope, secondScope, same, inside, rest⟩ := ih tail
          subst same
          exact ⟨middle, _, secondScope, rfl, .spent inside, rest⟩

/-- Handler capture uses the same split, including cuts across callback return
markers. The captured exit mode is a conclusion of the actual source checks. -/
theorem ModePending.handler_cut
    (cut : HandlerCut requested whole captured tail handler)
    (checked : ModePending outward actions phases world tables families whole scope outside before after) :
    ∃ (middle : UseMode) (capturedScope tailScope : SourceDependencyCapture.Scope),
      scope = capturedScope.append tailScope ∧
      ModePending outward actions phases world tables families captured capturedScope (tailScope.append outside) before middle ∧
      ModePending outward actions phases world tables families tail tailScope outside middle after := by
  rw [handler_cut_reconstructs cut] at checked
  exact checked.split

/-- Existing authenticated abandonment supplies these mode-aware checks
without adding checks for the ordinary code it skips. -/
theorem ModePending.of_unwind
    (source : SourceDependencyFrames.UnwindSource operations policy contracts tables families world stack demand requirements scope)
    (checked : Unwind outward actions phases world scope outside) :
    ModePending outward actions phases world tables families stack scope outside .unwind .unwind := by
  induction source generalizing outside with
  | nil => exact .nil
  | plain tail ih => cases checked with | plain rest => exact .push .skipped (ih rest)
  | handler declaration tail ih => cases checked with | handler rest => exact .push .handler (ih rest)
  | cell tail ih => cases checked with | cell rest => exact .push .cell (ih rest)
  | cleanup callback tail ih => cases checked with | cleanup code rest => exact .push (.armed code) (ih rest)
  | live saved tail ihSaved ihTail => cases checked with
      | live inside rest => exact .opening (ihSaved inside) (ihTail rest)
  | spent tail ih => cases checked with | spent rest => exact .spent (ih rest)
  | retiring tail ih => cases checked with | running rest => exact .push .retiring (ih rest)

/-- Ordinary source segments embed with their existing contextual checks.
The new mode distinction does not remove any ordinary source constructor. -/
theorem ModePending.of_ordinary
    (source : SourceDependencyFrames.Segment operations policy contracts tables families actions world
      stack input output demand requirements records scope incoming outgoing)
    (checked : Pending outward actions phases world scope outside) :
    ModePending outward actions phases world tables families stack scope outside .ordinary .ordinary := by
  induction source generalizing outside with
  | nil bound => exact .nil
  | push frame tail bound ih => cases frame with
      | plain => cases checked with | plain code rest => exact .push (.plain code) (ih rest)
      | handler => cases checked with | handler rest => exact .push .handler (ih rest)
      | cell => cases checked with | cell rest => exact .push .cell (ih rest)
      | armed => cases checked with | cleanup code rest => exact .push (.armed code) (ih rest)
      | running => cases checked with | running rest => exact .push .running (ih rest)
      | closing => cases checked with | running rest => exact .push .closing (ih rest)
      | retiring => cases checked with | running rest => exact .push .retiring (ih rest)
  | live known actionKnown inputAnnotation answerAnnotation caller held saved savedBound tail resume close bound ihSaved ihTail =>
      cases checked with | live inside rest => exact .live (ihSaved inside) (ihTail rest)
  | spent known annotation caller tail bound ih => cases checked with | spent rest => exact .spent (ih rest)

/-- Entry changes from abandonment to callback evaluation; its return marker
restores the previously checked unwind mode. -/
theorem ModePending.start_cleanup
    (checked : ModePending outward actions phases world tables families
      (.push (.armed action) rest) scope outside .unwind finalMode) :
    ∃ (dependencies : Dependencies) (restScope : SourceDependencyCapture.Scope),
      scope = .cleanup action.requests dependencies restScope ∧
      Local outward actions phases world (.sequence .pure (.sequence .pure dependencies)) (.running (restScope.append outside)) ∧
      ModePending outward actions phases world tables families (.push (.unwinding action) rest)
        (.running restScope) outside .ordinary finalMode := by
  cases checked with | push frame tail => cases frame with
    | armed callback => exact ⟨_, _, rfl, .sequence .pure (.sequence .pure callback), .push .unwinding tail⟩

/-- Unit return exposes precisely the abandoned suffix checked beneath the
callback marker, at unwind mode rather than ordinary return mode. -/
theorem ModePending.finish_cleanup
    (checked : ModePending outward actions phases world tables families
      (.push (.unwinding action) rest) scope outside .ordinary finalMode) :
    ∃ restScope, scope = .running restScope ∧
      ModePending outward actions phases world tables families rest restScope outside .unwind finalMode := by
  cases checked with | push frame tail => cases frame with
    | unwinding => exact ⟨_, rfl, tail⟩

end Ash.OneShot.SourceDependencyChecks.Lexical
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ModeFrame.realizes
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ModePending.realizes
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ModePending.append
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ModePending.return_mode
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ModePending.advance

#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ModePending.split
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ModePending.handler_cut
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ModePending.of_unwind
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ModePending.of_ordinary
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ModePending.start_cleanup
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ModePending.finish_cleanup


namespace Ash.OneShot.SourceDependencySchemes.Closing
/-- A ticket records the dependency annotation of its saved source. This
structural judgment connects that annotation to every live boundary, including
dormant ones; it imposes no condition on future executions. -/
inductive Bound (annotations : Nat → Option SourceDependencyCapture.Scope) : SourceDependencyCapture.Scope → Prop where
  | nil : Bound annotations .nil
  | plain (rest : Bound annotations tail) : Bound annotations (.plain dependencies tail)
  | handler (rest : Bound annotations tail) : Bound annotations (.handler effect table families tail)
  | cell (rest : Bound annotations tail) : Bound annotations (.cell identity tail)
  | cleanup (rest : Bound annotations tail) : Bound annotations (.cleanup needs dependencies tail)
  | running (rest : Bound annotations tail) : Bound annotations (.running tail)
  | live (recorded : annotations owner = some captured)
      (saved : Bound annotations captured) (rest : Bound annotations tail) :
      Bound annotations (.live owner captured tail)
  | spent (rest : Bound annotations tail) : Bound annotations (.spent owner tail)

end Ash.OneShot.SourceDependencySchemes.Closing


namespace Ash.OneShot.SourceDependencyChecks.Lexical
open ScopedExpressions ScopedExecution
open SourceDependencyAnnotations (Dependencies)
/-- Returning through a plain evaluation frame exposes its original checked
context and preserves the caller's actual final return mode. -/
theorem ModePending.pop_plain
    (checked : ModePending outward actions phases world tables families
      (.push (.plain plain) rest) scope outside .ordinary finalMode) :
    ∃ (dependencies : Dependencies) (restScope : SourceDependencyCapture.Scope),
      scope = .plain dependencies restScope ∧
      Local outward actions phases world dependencies (restScope.append outside) ∧
      ModePending outward actions phases world tables families rest restScope outside .ordinary finalMode := by
  cases checked with | push frame tail => cases frame with
    | plain code => exact ⟨_, _, rfl, code, tail⟩
end Ash.OneShot.SourceDependencyChecks.Lexical
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ModePending.pop_plain


namespace Ash.OneShot.SourceDependencyChecks.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyCapture (Scope Realizes OwnerCut OwnerSelection ResumeChecked)
open SourceDependencyAnnotations (Dependencies)
open LexicalUnwind (UseMode)
open OwnerPhaseTransitions (Phases spend)

/-- Return markers retain their distinct mode transitions in source annotations.
Their erasure is the existing protected lexical scope, not a new operation. -/
inductive ReturnBoundary where
  | normal | unwind | close | retire

def ReturnBoundary.apply : ReturnBoundary → UseMode → UseMode
  | .normal, mode | .retire, mode => mode
  | .unwind, _ => .unwind
  | .close, _ => .ordinary

inductive ReturnBoundary.Frame : ReturnBoundary → ExecFrame → Prop where
  | normal : ReturnBoundary.Frame .normal (.running action value closed)
  | unwind : ReturnBoundary.Frame .unwind (.unwinding action)
  | close : ReturnBoundary.Frame .close (.closing identity caller)
  | retire : ReturnBoundary.Frame .retire (.retiring owner)

inductive ReturnHints : SourceDependencyCapture.Scope → Type where
  | nil : ReturnHints .nil
  | plain : ReturnHints rest → ReturnHints (.plain dependencies rest)
  | handler : ReturnHints rest → ReturnHints (.handler effect table families rest)
  | cell : ReturnHints rest → ReturnHints (.cell identity rest)
  | cleanup : ReturnHints rest → ReturnHints (.cleanup needs callback rest)
  | running : ReturnBoundary → ReturnHints rest → ReturnHints (.running rest)
  | live : ReturnHints captured → ReturnHints rest → ReturnHints (.live owner captured rest)
  | spent : ReturnHints rest → ReturnHints (.spent owner rest)

namespace ReturnHints

def append : ReturnHints first → ReturnHints second → ReturnHints (first.append second)
  | .nil, tail => tail
  | .plain rest, tail => .plain (rest.append tail)
  | .handler rest, tail => .handler (rest.append tail)
  | .cell rest, tail => .cell (rest.append tail)
  | .cleanup rest, tail => .cleanup (rest.append tail)
  | .running kind rest, tail => .running kind (rest.append tail)
  | .live captured rest, tail => .live captured (rest.append tail)
  | .spent rest, tail => .spent (rest.append tail)

def returnMode : ReturnHints scope → UseMode → UseMode
  | .nil, mode => mode
  | .plain rest, mode | .handler rest, mode | .cell rest, mode | .cleanup rest, mode | .spent rest, mode => rest.returnMode mode
  | .running kind rest, mode => rest.returnMode (kind.apply mode)
  | .live captured rest, mode => rest.returnMode (captured.returnMode mode)

inductive MatchesStack (tables : CallableProtectionFrames.Tables) (families : SourceDependencyCapture.Families) :
    Stack → {scope : SourceDependencyCapture.Scope} → ReturnHints scope → Prop where
  | nil : MatchesStack tables families .nil .nil
  | plain (tail : MatchesStack tables families rest hints) :
      MatchesStack tables families (.push (.plain data) rest) (.plain (dependencies := dependencies) hints)
  | handler (tail : MatchesStack tables families rest hints) :
      MatchesStack tables families (.push (.handler data) rest)
        (.handler (effect := data.effectInst) (table := tables data) (families := families data) hints)
  | cell (tail : MatchesStack tables families rest hints) :
      MatchesStack tables families (.push (.cell identity payload caller answer) rest) (.cell (identity := identity) hints)
  | cleanup (tail : MatchesStack tables families rest hints) :
      MatchesStack tables families (.push (.armed action) rest) (.cleanup (needs := action.requests) (callback := callback) hints)
  | running (frame : ReturnBoundary.Frame kind entry) (tail : MatchesStack tables families rest hints) :
      MatchesStack tables families (.push entry rest) (.running kind hints)
  | live (saved : MatchesStack tables families captured capturedHints) (tail : MatchesStack tables families rest hints) :
      MatchesStack tables families (.live owner input answer captured caller rest) (.live (owner := owner) capturedHints hints)
  | spent (tail : MatchesStack tables families rest hints) :
      MatchesStack tables families (.spent owner answer caller rest) (.spent (owner := owner) hints)

abbrev Matches (tables : CallableProtectionFrames.Tables) (families : SourceDependencyCapture.Families)
    {scope : SourceDependencyCapture.Scope} (hints : ReturnHints scope) (stack : Stack) : Prop :=
  MatchesStack tables families stack hints

theorem Matches.erases {hints : ReturnHints scope} (source : Matches tables families hints stack) :
    Realizes tables families scope stack := by
  induction source with
  | nil => exact .nil
  | plain tail ih => exact .push .plain ih
  | handler tail ih => exact .push .handler ih
  | cell tail ih => exact .push .cell ih
  | cleanup tail ih => exact .push .cleanup ih
  | running frame tail ih => cases frame with
      | normal => exact .push .running ih
      | unwind => exact .push .unwinding ih
      | close => exact .push .closing ih
      | retire => exact .push .retiring ih
  | live saved tail ihSaved ihTail => exact .live ihSaved ihTail
  | spent tail ih => exact .spent ih

theorem Matches.return_mode (source : Matches tables families hints stack) :
    hints.returnMode mode = LexicalUnwind.returnMode stack mode := by
  induction source generalizing mode with
  | nil => rfl
  | plain tail ih | handler tail ih | cell tail ih | cleanup tail ih | spent tail ih => exact ih
  | running frame tail ih => cases frame <;> exact ih
  | live saved tail ihSaved ihTail => simp only [returnMode, LexicalUnwind.returnMode, ihSaved, ihTail]

theorem Matches.append (first : Matches tables families firstHints a) (second : Matches tables families secondHints b) :
    Matches tables families (firstHints.append secondHints) (a.append b) := by
  induction first with
  | nil => exact second
  | plain tail ih => exact .plain ih
  | handler tail ih => exact .handler ih
  | cell tail ih => exact .cell ih
  | cleanup tail ih => exact .cleanup ih
  | running frame tail ih => exact .running frame ih
  | live saved tail ihSaved ihTail => exact .live saved ihTail
  | spent tail ih => exact .spent ih

/-- A source annotation determines the same physical split, retaining marker
kinds. It does not select another handler or infer metadata from a result type. -/
theorem Matches.split (source : Matches tables families (firstHints.append secondHints) stack) :
    ∃ a b, stack = a.append b ∧ Matches tables families firstHints a ∧ Matches tables families secondHints b := by
  induction firstHints generalizing stack with
  | nil => exact ⟨.nil, stack, rfl, .nil, source⟩
  | plain rest ih => cases source with | plain tail =>
      obtain ⟨a, b, rfl, first, second⟩ := ih tail
      exact ⟨.push _ a, b, rfl, .plain first, second⟩
  | handler rest ih => cases source with | handler tail =>
      obtain ⟨a, b, rfl, first, second⟩ := ih tail
      exact ⟨.push _ a, b, rfl, .handler first, second⟩
  | cell rest ih => cases source with | cell tail =>
      obtain ⟨a, b, rfl, first, second⟩ := ih tail
      exact ⟨.push _ a, b, rfl, .cell first, second⟩
  | cleanup rest ih => cases source with | cleanup tail =>
      obtain ⟨a, b, rfl, first, second⟩ := ih tail
      exact ⟨.push _ a, b, rfl, .cleanup first, second⟩
  | running kind rest ih => cases source with | running frame tail =>
      obtain ⟨a, b, rfl, first, second⟩ := ih tail
      exact ⟨.push _ a, b, rfl, .running frame first, second⟩
  | live saved rest ihSaved ihRest => cases source with | live inside tail =>
      obtain ⟨a, b, rfl, first, second⟩ := ihRest tail
      exact ⟨.live _ _ _ _ _ a, b, rfl, .live inside first, second⟩
  | spent rest ih => cases source with | spent tail =>
      obtain ⟨a, b, rfl, first, second⟩ := ih tail
      exact ⟨.spent _ _ _ a, b, rfl, .spent first, second⟩

/-- Split an annotation at an already identified physical prefix. The old
lexical realization fixes its length and constructors; marker kinds remain in
this annotation. -/
theorem Matches.split_at {firstHints : ReturnHints firstScope}
    (first : Realizes tables families firstScope a)
    (source : Matches tables families (firstHints.append secondHints) (a.append b)) :
    Matches tables families firstHints a ∧ Matches tables families secondHints b := by
  induction first generalizing b with
  | nil => cases firstHints; exact ⟨.nil, source⟩
  | push frame tail ih =>
      cases frame <;> cases firstHints <;> cases source
      all_goals
        obtain ⟨inside, outside⟩ := ih ‹_›
        refine ⟨?_, outside⟩
        first
        | exact .plain inside
        | exact .handler inside
        | exact .cell inside
        | exact .cleanup inside
        | exact .running ‹_› inside
  | live saved tail ihSaved ihTail => cases firstHints with | live inside rest =>
      cases source with | live savedMatch later =>
        obtain ⟨firstMatch, outside⟩ := ihTail later
        exact ⟨.live savedMatch firstMatch, outside⟩
  | spent tail ih => cases firstHints with | spent rest =>
      cases source with | spent later =>
        obtain ⟨inside, outside⟩ := ih later
        exact ⟨.spent inside, outside⟩

end ReturnHints
end Ash.OneShot.SourceDependencyChecks.Lexical
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Matches.erases
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Matches.return_mode
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Matches.append
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Matches.split

namespace Ash.OneShot.SourceDependencyChecks.Lexical
open ScopedExpressions ScopedExecution SourceDependencyAnnotations
open SourceDependencyCapture (OwnerCut OwnerSelection ResumeChecked)
open OwnerPhaseTransitions (Phases spend)
open LexicalUnwind (UseMode)

namespace ReturnHints

/-- Finite source traversal at the annotated entry mode. Callback bodies retain
the existing local checks; skipped ordinary code contributes no obligation. -/
inductive Pending (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : Phases) (world : List Nat) :
    {scope outside : SourceDependencyCapture.Scope} →
    ReturnHints scope → ReturnHints outside → UseMode → UseMode → Prop where
  | nil : Pending outward actions phases world .nil outside mode mode
  | plain {rest : ReturnHints restScope} {outside : ReturnHints outsideScope}
      (code : Local outward actions phases world dependencies (restScope.append outsideScope))
      (tail : Pending outward actions phases world rest outside .ordinary finalMode) :
      Pending outward actions phases world (.plain (dependencies := dependencies) (rest := restScope) rest)
        (outside : ReturnHints outsideScope) .ordinary finalMode
  | skipped (tail : Pending outward actions phases world rest outside .unwind finalMode) :
      Pending outward actions phases world (.plain rest) outside .unwind finalMode
  | handler (tail : Pending outward actions phases world rest outside mode finalMode) :
      Pending outward actions phases world (.handler rest) outside mode finalMode
  | cell (tail : Pending outward actions phases world rest outside mode finalMode) :
      Pending outward actions phases world (.cell rest) outside mode finalMode
  | cleanup {rest : ReturnHints restScope} {outside : ReturnHints outsideScope}
      (callback : Local outward actions phases world dependencies (.running (restScope.append outsideScope)))
      (tail : Pending outward actions phases world rest outside mode finalMode) :
      Pending outward actions phases world (.cleanup (callback := dependencies) (rest := restScope) rest)
        (outside : ReturnHints outsideScope) mode finalMode
  | normal (tail : Pending outward actions phases world rest outside .ordinary finalMode) :
      Pending outward actions phases world (.running .normal rest) outside .ordinary finalMode
  | unwinding (tail : Pending outward actions phases world rest outside .unwind finalMode) :
      Pending outward actions phases world (.running .unwind rest) outside .ordinary finalMode
  | closing (tail : Pending outward actions phases world rest outside .ordinary finalMode) :
      Pending outward actions phases world (.running .close rest) outside mode finalMode
  | retiring (tail : Pending outward actions phases world rest outside mode finalMode) :
      Pending outward actions phases world (.running .retire rest) outside mode finalMode
  | live (saved : Pending outward actions phases world captured (rest.append outside) .ordinary middle)
      (tail : Pending outward actions phases world rest outside middle finalMode) :
      Pending outward actions phases world (.live captured rest) outside .ordinary finalMode
  | opening (saved : Pending outward actions phases world captured (.running .retire (rest.append outside)) .unwind .unwind)
      (tail : Pending outward actions phases world rest outside .unwind finalMode) :
      Pending outward actions phases world (.live captured rest) outside .unwind finalMode
  | spent (tail : Pending outward actions phases world rest outside mode finalMode) :
      Pending outward actions phases world (.spent rest) outside mode finalMode

theorem Pending.return_mode
    (checked : Pending outward actions phases world hints outside before after) : hints.returnMode before = after := by
  induction checked with
  | nil => rfl
  | plain code tail ih => exact ih
  | skipped tail ih => exact ih
  | handler tail ih => exact ih
  | cell tail ih => exact ih
  | cleanup callback tail ih => exact ih
  | normal tail ih => exact ih
  | unwinding tail ih => exact ih
  | closing tail ih => exact ih
  | retiring tail ih => exact ih
  | spent tail ih => exact ih
  | live saved tail ihSaved ihTail | opening saved tail ihSaved ihTail =>
      simpa only [returnMode, ihSaved] using ihTail

/-- The annotated source traversal is interpreted on the same physical stack.
No successor safety or successful execution is a premise. -/
theorem Pending.realized {hints : ReturnHints scope} {outside : ReturnHints outsideScope}
    (checked : Pending outward actions phases world hints outside before after)
    (matching : Matches tables families hints stack) :
    ModePending outward actions phases world tables families stack scope outsideScope before after := by
  induction checked generalizing stack with
  | nil => cases matching; exact .nil
  | plain code tail ih => cases matching with | plain later => exact .push (.plain code) (ih later)
  | skipped tail ih => cases matching with | plain later => exact .push .skipped (ih later)
  | handler tail ih => cases matching with | handler later => exact .push .handler (ih later)
  | cell tail ih => cases matching with | cell later => exact .push .cell (ih later)
  | cleanup callback tail ih => cases matching with | cleanup later => exact .push (.armed callback) (ih later)
  | normal tail ih => cases matching with | running frame later => cases frame; exact .push .running (ih later)
  | unwinding tail ih => cases matching with | running frame later => cases frame; exact .push .unwinding (ih later)
  | closing tail ih => cases matching with | running frame later => cases frame; exact .push .closing (ih later)
  | retiring tail ih => cases matching with | running frame later => cases frame; exact .push .retiring (ih later)
  | live saved tail ihSaved ihTail => cases matching with | live inside later => exact .live (ihSaved inside) (ihTail later)
  | opening saved tail ihSaved ihTail => cases matching with | live inside later => exact .opening (ihSaved inside) (ihTail later)
  | spent tail ih => cases matching with | spent later => exact .spent (ih later)

/-- A local resume rule over source annotations, with independent access,
permission and one-shot phase checking. The restored finite source is checked
at its actual return modes; no ordinary-only pending premise is imposed. -/
inductive Resume (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : Phases) (world : List Nat) (owner : Nat) :
    {scope : SourceDependencyCapture.Scope} → ReturnHints scope → UseMode → Prop where
  | checked {front : ReturnHints frontScope} {captured : ReturnHints capturedScope} {tail : ReturnHints tailScope}
      (located : OwnerCut owner (frontScope.append (.live owner capturedScope tailScope))
        ⟨frontScope, capturedScope, tailScope⟩)
      (known : actions owner = some rights) (permission : rights.resume = true)
      (available : phases owner = .available)
      (restored : Pending outward actions (spend phases owner) world
        (captured.append (front.append (.spent (owner := owner) tail))) .nil .ordinary finalMode) :
      Resume outward actions phases world owner (front.append (.live (owner := owner) captured tail)) finalMode

/-- The structural source rule produces the actual resumption step and the
mixed retained checks. Runtime owner accounting is reused separately. -/
theorem Resume.step {hints : ReturnHints scope}
    (admitted : Resume outward actions phases world owner hints finalMode)
    (matching : Matches tables families hints stack)
    (resolved : runtimeScope.resolve binder = some owner) (closed : ClosedValue value) :
    ∃ nextScope, ∃ nextHints : ReturnHints nextScope, ∃ nextStack,
      RawStep ⟨.resume binder value, runtimeScope, stack⟩ ⟨value, runtimeScope, nextStack⟩ [] [.ticket owner] ∧
      Matches tables families nextHints nextStack ∧
      Pending outward actions (spend phases owner) world nextHints .nil .ordinary finalMode ∧
      ModePending outward actions (spend phases owner) world tables families nextStack nextScope .nil .ordinary finalMode := by
  cases admitted with
  | checked located known permission available restored =>
      obtain ⟨front, boundary, rfl, prefixSource, boundarySource⟩ := matching.split
      cases boundarySource with
      | live inside outside =>
          rename_i capturedStack restStack inputType answerType callerScope
          have afterSource := Matches.append inside (Matches.append prefixSource
            (.spent (owner := owner) (answer := answerType) (caller := callerScope) outside))
          exact ⟨_, _, _, .resume binder owner runtimeScope _ _ _ front _ _ value closed resolved,
            afterSource, restored, restored.realized afterSource⟩

end ReturnHints
end Ash.OneShot.SourceDependencyChecks.Lexical
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Pending.return_mode
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Pending.realized
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Resume.step

namespace Ash.OneShot.SourceDependencyChecks.Lexical
open ScopedExpressions ScopedExecution SourceDependencyAnnotations

/-- Existing mixed source checks supply the annotations and their finite
traversal together. No marker is guessed from its erased protected scope. -/
theorem ModePending.annotate_return {outsideHints : ReturnHints outside}
    (checked : ModePending outward actions phases world tables families stack scope outside before after) :
    ∃ hints : ReturnHints scope, ReturnHints.Matches tables families hints stack ∧
      ReturnHints.Pending outward actions phases world hints outsideHints before after := by
  induction checked with
  | nil => exact ⟨.nil, .nil, .nil⟩
  | push frame tail ih =>
      obtain ⟨rest, matched, checked⟩ := ih (outsideHints := outsideHints)
      cases frame with
      | plain code => exact ⟨.plain rest, .plain matched, .plain code checked⟩
      | skipped => exact ⟨.plain rest, .plain matched, .skipped checked⟩
      | handler => exact ⟨.handler rest, .handler matched, .handler checked⟩
      | cell => exact ⟨.cell rest, .cell matched, .cell checked⟩
      | armed callback => exact ⟨.cleanup rest, .cleanup matched, .cleanup callback checked⟩
      | running => exact ⟨.running .normal rest, .running .normal matched, .normal checked⟩
      | unwinding => exact ⟨.running .unwind rest, .running .unwind matched, .unwinding checked⟩
      | closing => exact ⟨.running .close rest, .running .close matched, .closing checked⟩
      | retiring => exact ⟨.running .retire rest, .running .retire matched, .retiring checked⟩
  | live saved tail ihSaved ihTail =>
      obtain ⟨rest, matched, checked⟩ := ihTail (outsideHints := outsideHints)
      obtain ⟨inside, savedMatch, savedCheck⟩ := ihSaved (outsideHints := rest.append outsideHints)
      exact ⟨.live inside rest, .live savedMatch matched, .live savedCheck checked⟩
  | opening saved tail ihSaved ihTail =>
      obtain ⟨rest, matched, checked⟩ := ihTail (outsideHints := outsideHints)
      obtain ⟨inside, savedMatch, savedCheck⟩ := ihSaved (outsideHints := .running .retire (rest.append outsideHints))
      exact ⟨.live inside rest, .live savedMatch matched, .opening savedCheck checked⟩
  | spent tail ih =>
      obtain ⟨rest, matched, checked⟩ := ih (outsideHints := outsideHints)
      exact ⟨.spent rest, .spent matched, .spent checked⟩

namespace ReturnExamples
open ScopedExpressions ScopedExecution SourceDependencyCapture
open OwnerPhaseTransitions (available spend)

def actions : Syntax.UsageTickets := fun owner => if owner = 7 then some ⟨true, false⟩ else none

def savedScope : SourceDependencyCapture.Scope := .running (.plain (.invoke ⟨99, .resume⟩) .nil)

def savedHints : ReturnHints savedScope := .running .unwind (.plain .nil)

/-- The ordinary code mentions an unrelated owner, but returning into cleanup
skips that code. This is accepted without inventing a capability for owner 99. -/
theorem resume_into_cleanup : ReturnHints.Resume [] actions (available [7]) [] 7
    (.live (owner := 7) savedHints .nil) .unwind := by
  apply ReturnHints.Resume.checked (front := .nil)
  · exact .hit
  · exact (show actions 7 = some ⟨true, false⟩ by simp [actions])
  · rfl
  · simp [available]
  · exact .unwinding (.skipped (.spent .nil))

theorem ordinary_pending_rejects_skipped_code :
    ¬ Pending [] actions (spend (available [7]) 7) []
      (savedScope.append (.spent 7 .nil)) .nil := by
  intro checked
  cases checked with | running tail =>
    cases tail with | plain code tail =>
      cases code with | resume access restored =>
        cases access with | checked located known permission ready =>
          cases located with | spent later => cases later

/-- The new source rule supplies the same raw resume step and mixed checks for
its real callback-return marker. This is a local case, not initial admission. -/
theorem actual_resume_into_cleanup (action : ActionData) (data : PlainData)
    (tables : CallableProtectionFrames.Tables) (families : Families) :
    ∃ nextScope, ∃ nextHints : ReturnHints nextScope, ∃ nextStack,
      RawStep
        ⟨.resume 3 .unit, .ticket 3 7,
          .live 7 .unit .unit (.push (.unwinding action) (.push (.plain data) .nil)) .none .nil⟩
        ⟨.unit, .ticket 3 7, nextStack⟩ [] [.ticket 7] ∧
      ReturnHints.Matches tables families nextHints nextStack ∧
      ReturnHints.Pending [] actions (spend (available [7]) 7) [] nextHints .nil .ordinary .unwind ∧
      ModePending [] actions (spend (available [7]) 7) [] tables families nextStack nextScope .nil .ordinary .unwind := by
  exact resume_into_cleanup.step
    (.live (.running .unwind (.plain .nil)) .nil) rfl ScopedExecution.Examples.unit_closed

end ReturnExamples
end Ash.OneShot.SourceDependencyChecks.Lexical
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ModePending.annotate_return
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnExamples.resume_into_cleanup
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnExamples.ordinary_pending_rejects_skipped_code
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnExamples.actual_resume_into_cleanup

namespace Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints
open ScopedExecution SourceDependencyCapture
open OwnerPhaseTransitions (spend)

/-- The corrected local rule checks the successor of an independently known
owner cut. Existing deterministic lexical lookup identifies the same cut. -/
theorem Resume.at_cut {hints : ReturnHints scope}
    (admitted : Resume outward actions phases world owner hints finalMode)
    (matching : Matches tables families hints
      (front.append (.live owner input answer captured caller tail)))
    (cut : OwnerCut owner scope ⟨frontScope, capturedScope, tailScope⟩)
    (frontSource : Realizes tables families frontScope front) :
    ∃ nextHints : ReturnHints (capturedScope.append (frontScope.append (.spent owner tailScope))),
      Matches tables families nextHints (captured.append (front.append (.spent owner answer caller tail))) ∧
      Pending outward actions (spend phases owner) world nextHints .nil .ordinary finalMode ∧
      ModePending outward actions (spend phases owner) world tables families
        (captured.append (front.append (.spent owner answer caller tail)))
        (capturedScope.append (frontScope.append (.spent owner tailScope))) .nil .ordinary finalMode := by
  cases admitted with
  | checked located known permission available restored =>
      have same := Option.some.inj (located.lookup.symm.trans cut.lookup)
      obtain ⟨rfl, rfl, rfl⟩ := OwnerSelection.mk.inj same
      obtain ⟨first, boundary⟩ := matching.split_at frontSource
      cases boundary with
      | live inside outside =>
          have next := Matches.append inside (Matches.append first (.spent (owner := owner) (answer := answer) (caller := caller) outside))
          exact ⟨_, next, restored, restored.realized next⟩
end Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Matches.split_at
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Resume.at_cut


namespace Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies Expression)
open SourceDependencyCapture (OwnerCut OwnerSelection Realizes)
open OwnerPhaseTransitions (Phases spend)
open LexicalUnwind (UseMode)

/-- Cleanup returns to the mode in which its scope was left. -/
def callbackBoundary : UseMode → ReturnBoundary
  | .ordinary => .normal
  | .unwind => .unwind

mutual
/-- Recursive dependency checks use the same annotated lexical scopes in
ordinary code, handler bodies, callbacks and restored continuations. -/
inductive Local (outward : List Instance) (actions : Syntax.UsageTickets) :
    Phases → List Nat → Dependencies → {scope : SourceDependencyCapture.Scope} → ReturnHints scope → Prop where
  | pure : Local outward actions phases world .pure hints
  | request {hints : ReturnHints scope}
      (checked : Lexical.Capture scope effect operation)
      (callbacks : ∀ {capturedScope tailScope} (captured : ReturnHints capturedScope)
        (tail : ReturnHints tailScope) contract modes,
        HEq hints (captured.append tail) →
        SourceDependencyCapture.select effect operation scope = some (.handler capturedScope tailScope contract modes) →
        contract.dispose = true →
        Pending outward actions phases world captured (.running .close tail) .unwind .unwind)
      (ownerBound : ∀ captured tail contract modes,
        SourceDependencyCapture.select effect operation scope = some (.handler captured tail contract modes) →
        contract.dispose = true → SourceDependencyOwners.PendingWithin world
          (SourceDependencyOwners.owners captured) captured) :
      Local outward actions phases world (.request effect operation) hints
  | resume {front : ReturnHints frontScope} {captured : ReturnHints capturedScope} {tail : ReturnHints tailScope}
      (located : OwnerCut owner (frontScope.append (.live owner capturedScope tailScope))
        ⟨frontScope, capturedScope, tailScope⟩)
      (known : actions owner = some rights) (permission : rights.resume = true)
      (available : phases owner = .available)
      (restored : Pending outward actions (spend phases owner) world
        (captured.append (front.append (.spent (owner := owner) tail))) .nil .ordinary
        ((front.append (.live (owner := owner) captured tail)).returnMode .ordinary)) :
      Local outward actions phases world (.invoke ⟨owner, .resume⟩)
        (front.append (.live (owner := owner) captured tail))
  | dispose {front : ReturnHints frontScope} {captured : ReturnHints capturedScope} {tail : ReturnHints tailScope}
      (located : OwnerCut owner (frontScope.append (.live owner capturedScope tailScope))
        ⟨frontScope, capturedScope, tailScope⟩)
      (known : actions owner = some rights) (permission : rights.dispose = true)
      (available : phases owner = .available) (unprotected : capturedScope.held = false)
      (abandoned : Pending outward actions (spend phases owner) world captured
        (.running .close (front.append (.spent (owner := owner) tail))) .unwind .unwind)
      (waiting : Pending outward actions (spend phases owner) world
        (front.append (.spent (owner := owner) tail)) .nil .ordinary
        ((front.append (.live (owner := owner) captured tail)).returnMode .ordinary)) :
      Local outward actions phases world (.invoke ⟨owner, .dispose⟩)
        (front.append (.live (owner := owner) captured tail))
  | sequence (first : Local outward actions phases world before (.plain (dependencies := after) hints))
      (second : Local outward actions phases world after hints) :
      Local outward actions phases world (.sequence before after) hints
  | choice (left : Local outward actions phases world first hints)
      (right : Local outward actions phases world second hints) :
      Local outward actions phases world (.choice first second) hints
  | handler (body : Local outward actions phases world dependencies
        (.handler (effect := effect) (table := table) (families := families) hints)) :
      Local outward actions phases world (.handler effect table families dependencies) hints
  | cleanup (body : Local outward actions phases world dependencies
        (.cleanup (needs := needs) (callback := callback) hints))
      (completion : Local outward actions phases world callback (.running .normal hints)) :
      Local outward actions phases world (.cleanup needs callback dependencies) hints
  | resource (body : ∀ identity, identity ∉ world →
      Local outward actions phases (world ++ [identity]) (family identity) (.cell (identity := identity) hints)) :
      Local outward actions phases world (.resource family) hints

/-- This traversal checks executed code with the recursive Local judgment.
Callbacks see their actual normal-return or unwind-return marker. -/
inductive Pending (outward : List Instance) (actions : Syntax.UsageTickets) :
    Phases → List Nat → {scope outside : SourceDependencyCapture.Scope} →
    ReturnHints scope → ReturnHints outside → UseMode → UseMode → Prop where
  | nil : Pending outward actions phases world .nil outside mode mode
  | plain {rest : ReturnHints restScope} {outside : ReturnHints outsideScope}
      (code : Local outward actions phases world dependencies (rest.append outside))
      (tail : Pending outward actions phases world rest outside .ordinary finalMode) :
      Pending outward actions phases world (.plain (dependencies := dependencies) rest) outside .ordinary finalMode
  | skipped (tail : Pending outward actions phases world rest outside .unwind finalMode) :
      Pending outward actions phases world (.plain rest) outside .unwind finalMode
  | handler (tail : Pending outward actions phases world rest outside mode finalMode) :
      Pending outward actions phases world (.handler rest) outside mode finalMode
  | cell (tail : Pending outward actions phases world rest outside mode finalMode) :
      Pending outward actions phases world (.cell rest) outside mode finalMode
  | cleanup {rest : ReturnHints restScope} {outside : ReturnHints outsideScope}
      (callback : Local outward actions phases world dependencies
        (.running (callbackBoundary mode) (rest.append outside)))
      (tail : Pending outward actions phases world rest outside mode finalMode) :
      Pending outward actions phases world (.cleanup (callback := dependencies) rest) outside mode finalMode
  | normal (tail : Pending outward actions phases world rest outside .ordinary finalMode) :
      Pending outward actions phases world (.running .normal rest) outside .ordinary finalMode
  | unwinding (tail : Pending outward actions phases world rest outside .unwind finalMode) :
      Pending outward actions phases world (.running .unwind rest) outside .ordinary finalMode
  | closing (tail : Pending outward actions phases world rest outside .ordinary finalMode) :
      Pending outward actions phases world (.running .close rest) outside mode finalMode
  | retiring (tail : Pending outward actions phases world rest outside mode finalMode) :
      Pending outward actions phases world (.running .retire rest) outside mode finalMode
  | live (saved : Pending outward actions phases world captured (rest.append outside) .ordinary middle)
      (tail : Pending outward actions phases world rest outside middle finalMode) :
      Pending outward actions phases world (.live captured rest) outside .ordinary finalMode
  | opening (saved : Pending outward actions phases world captured (.running .retire (rest.append outside)) .unwind .unwind)
      (tail : Pending outward actions phases world rest outside .unwind finalMode) :
      Pending outward actions phases world (.live captured rest) outside .unwind finalMode
  | spent (tail : Pending outward actions phases world rest outside mode finalMode) :
      Pending outward actions phases world (.spent rest) outside mode finalMode
end

/-- Existing independent capability and phase checks still reject reuse. -/
theorem Local.consumed_resume_rejected :
    ¬ Local outward actions (spend phases owner) world (.invoke ⟨owner, .resume⟩) hints := by
  intro checked
  cases checked with | resume located known permission available restored =>
    simp only [OwnerPhaseTransitions.spend_self] at available
    cases available

theorem Local.consumed_dispose_rejected :
    ¬ Local outward actions (spend phases owner) world (.invoke ⟨owner, .dispose⟩) hints := by
  intro checked
  cases checked with | dispose located known permission available unprotected abandoned waiting =>
    simp only [OwnerPhaseTransitions.spend_self] at available
    cases available

/-- Source modes describe the existing runtime markers, independently of the
recursive capability checks on executed code. -/
theorem Pending.return_mode {hints : ReturnHints scope} {outside : ReturnHints outsideScope}
    (checked : Pending outward actions phases world hints outside before after) :
    hints.returnMode before = after := by
  induction hints generalizing outsideScope before after with
  | nil => cases checked; rfl
  | plain rest ih => cases checked with
    | plain code tail => exact ih tail
    | skipped tail => exact ih tail
  | handler rest ih => cases checked with | handler tail => exact ih tail
  | cell rest ih => cases checked with | cell tail => exact ih tail
  | cleanup rest ih => cases checked with | cleanup callback tail => exact ih tail
  | running kind rest ih => cases checked with
    | normal tail => exact ih tail
    | unwinding tail => exact ih tail
    | closing tail => exact ih tail
    | retiring tail => exact ih tail
  | live saved rest ihSaved ihTail => cases checked with
    | live inside tail => simpa only [ReturnHints.returnMode, ihSaved inside] using ihTail tail
    | opening inside tail => simpa only [ReturnHints.returnMode, ihSaved inside] using ihTail tail
  | spent rest ih => cases checked with | spent tail => exact ih tail

/-- Structural source inversion exposes the actual ready invocation, including
when it is the final dependency of an expression with a value operand. -/
theorem Local.ready_resume
    (current : Expression operations policy contracts world allowed runtimeScope environment
      (.resume binder value) result demand requirements dependencies)
    (resolved : runtimeScope.resolve binder = some owner)
    (checked : Local outward actions phases world dependencies hints) :
    Local outward actions phases world (.invoke ⟨owner, .resume⟩) hints := by
  cases current with | resume known actual permission operand admitted formed =>
    cases Option.some.inj (actual.symm.trans resolved)
    cases checked with | sequence first second => exact second

/-- Reuse the annotated primitive proof's lexical-cut argument with recursive
checks. The result keeps recursive checks in all resumed code and callbacks. -/
theorem Local.resume_at_cut {hints : ReturnHints scope}
    (admitted : Local outward actions phases world (.invoke ⟨owner, .resume⟩) hints)
    (matching : Matches tables families hints
      (front.append (.live owner input answer captured caller tail)))
    (cut : OwnerCut owner scope ⟨frontScope, capturedScope, tailScope⟩)
    (frontSource : Realizes tables families frontScope front) :
    ∃ nextHints : ReturnHints (capturedScope.append (frontScope.append (.spent owner tailScope))),
      Matches tables families nextHints (captured.append (front.append (.spent owner answer caller tail))) ∧
      Pending outward actions (spend phases owner) world nextHints .nil .ordinary (hints.returnMode .ordinary) := by
  cases admitted with
  | resume located known permission available restored =>
      have same := Option.some.inj (located.lookup.symm.trans cut.lookup)
      obtain ⟨rfl, rfl, rfl⟩ := OwnerSelection.mk.inj same
      obtain ⟨first, boundary⟩ := matching.split_at frontSource
      cases boundary with
      | live inside outside =>
          have next := Matches.append inside (Matches.append first (.spent (owner := owner) (answer := answer) (caller := caller) outside))
          exact ⟨_, next, restored⟩

/-- Executing a cleanup switches to its existing callback marker and returns
to the abandoned suffix. The callback is recursively checked in that scope. -/
theorem Pending.start_cleanup
    (checked : Pending outward actions phases world
      (.cleanup (needs := needs) (callback := dependencies) rest) outside .unwind finalMode) :
    Local outward actions phases world (.sequence .pure (.sequence .pure dependencies))
      (.running .unwind (rest.append outside)) ∧
    Pending outward actions phases world (.running .unwind rest) outside .ordinary finalMode := by
  cases checked with | cleanup callback tail =>
    exact ⟨.sequence .pure (.sequence .pure callback), .unwinding tail⟩

end Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local.consumed_resume_rejected
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local.consumed_dispose_rejected
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive.Pending.return_mode
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local.ready_resume
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local.resume_at_cut
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive.Pending.start_cleanup

namespace Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive
open ScopedExpressions ScopedExecution SourceDependencyCapture
open OwnerPhaseTransitions (spend)

/-- Lexical disposal keeps the recursively checked abandoned and waiting
segments under the actual closing boundary. No cleanup plan is constructed. -/
theorem Local.discard_step {hints : ReturnHints scope}
    (admitted : Local outward actions phases world (.invoke ⟨owner, .dispose⟩) hints)
    (matching : Matches tables families hints stack)
    (resolved : runtimeScope.resolve binder = some owner) :
    ∃ savedScope waitingScope, ∃ savedHints : ReturnHints savedScope,
    ∃ waitingHints : ReturnHints waitingScope, ∃ captured waiting,
      LexicalUnwind.Transition (.eval ⟨.discard binder, runtimeScope, stack⟩)
        (.unwind runtimeScope (captured.append (.push (.closing identity runtimeScope) waiting)))
        [.close identity] [.ticket owner] ∧
      Matches tables families savedHints captured ∧ Matches tables families waitingHints waiting ∧
      Pending outward actions (spend phases owner) world savedHints (.running .close waitingHints) .unwind .unwind ∧
      Pending outward actions (spend phases owner) world waitingHints .nil .ordinary (hints.returnMode .ordinary) := by
  cases admitted with
  | dispose located known permission available unprotected abandoned waiting =>
      obtain ⟨front, boundary, rfl, frontMatch, boundaryMatch⟩ := matching.split
      cases boundaryMatch with
      | live inside outside =>
          have saved := Matches.erases inside
          exact ⟨_, _, _, _, _, _, .discard binder owner identity runtimeScope _ _ _ front _ _ resolved
            (saved.held ▸ unprotected), inside,
            Matches.append frontMatch (.spent outside), abandoned, waiting⟩

/-- The physical cleanup step exposes the recursive callback judgment,
including its unwind-return annotation. -/
theorem Pending.cleanup_step
    (matching : Matches tables families hints (.push (.armed action) rest))
    (checked : Pending outward actions phases world hints .nil .unwind finalMode) :
    ∃ dependencies restScope, ∃ restHints : ReturnHints restScope,
      LexicalUnwind.Transition (.unwind runtimeScope (.push (.armed action) rest))
        (.eval ⟨.app action.action .unit, .none, .push (.unwinding action) rest⟩) [] [] ∧
      Matches tables families (.running .unwind restHints) (.push (.unwinding action) rest) ∧
      Local outward actions phases world (.sequence .pure (.sequence .pure dependencies))
        (.running .unwind (restHints.append .nil)) ∧
      Pending outward actions phases world (.running .unwind restHints) .nil .ordinary finalMode := by
  cases matching with
  | cleanup tail =>
      obtain ⟨callback, continued⟩ := checked.start_cleanup
      exact ⟨_, _, _, .startCleanup, .running .unwind tail, callback, continued⟩
  | running marker tail => cases marker

namespace Examples
open OwnerPhaseTransitions (available)
open Lexical.ReturnExamples (actions savedHints)

/-- The corrected rule composes under sequencing and a nested interpretation;
the saved unwind marker skips the unavailable owner's ordinary dependency. -/
theorem nested_handler_resume : Local [] actions (available [7]) []
    (.handler (.cell 42) [] [] (.sequence .pure (.invoke ⟨7, .resume⟩)))
    (.live (owner := 7) savedHints .nil) := by
  apply Local.handler
  apply Local.sequence .pure
  apply Local.resume (front := .handler (effect := .cell 42) (table := []) (families := []) .nil)
  · exact .handler .hit
  · exact (show actions 7 = some ⟨true, false⟩ by simp [actions])
  · rfl
  · simp [available]
  · exact .unwinding (.skipped (.handler (.spent .nil)))

/-- Recursive callback checking retains a handler and a nonempty caller prefix
around an invocation. No separate primitive-admission witness is supplied. -/
theorem callback_nested_resume : Pending [] actions (available [7]) []
    (.cleanup (needs := [])
      (callback := .handler (.cell 42) [] [] (.sequence .pure (.invoke ⟨7, .resume⟩)))
      (.live (owner := 7) .nil .nil)) .nil .ordinary .ordinary := by
  apply Pending.cleanup
  · apply Local.handler
    apply Local.sequence .pure
    apply Local.resume
      (front := .handler (effect := .cell 42) (table := []) (families := []) (.running .normal .nil))
    · exact .handler (.running .hit)
    · exact (show actions 7 = some ⟨true, false⟩ by simp [actions])
    · rfl
    · simp [available]
    · exact .handler (.normal (.spent .nil))
  · exact .live .nil .nil

end Examples
end Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local.discard_step
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive.Pending.cleanup_step
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive.Examples.nested_handler_resume
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive.Examples.callback_nested_resume

namespace Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive
/-- Reuse silence of value dependencies when reducing a sequencing prefix. -/
theorem Local.silent {hints : ReturnHints scope} (silent : dependencies.Silent) :
    Local outward actions phases world dependencies hints := by
  induction silent generalizing scope with
  | pure => exact .pure
  | sequence first second ihFirst ihSecond => exact .sequence ihFirst ihSecond

theorem Local.sequence_iff : Local outward actions phases world (.sequence first second) hints ↔
    Local outward actions phases world first (.plain (dependencies := second) hints) ∧
      Local outward actions phases world second hints := by
  constructor
  · intro checked; cases checked with | sequence left right => exact ⟨left, right⟩
  · intro ⟨left, right⟩; exact .sequence left right

theorem Local.silent_prefix (silent : first.Silent) :
    Local outward actions phases world (.sequence first second) hints ↔
      Local outward actions phases world second hints :=
  ⟨fun checked => (Local.sequence_iff.mp checked).2, fun checked => .sequence (.silent silent) checked⟩
end Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local.silent
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local.sequence_iff
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local.silent_prefix


namespace Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints
open SourceDependencyCapture (Scope)

private theorem congr_hints {layer : SourceDependencyCapture.Scope → SourceDependencyCapture.Scope} {a : ReturnHints first} {b : ReturnHints second}
    (same : first = second) (related : HEq a b)
    (f : ∀ {scope}, ReturnHints scope → ReturnHints (layer scope)) : HEq (f a) (f b) := by
  cases same
  cases eq_of_heq related
  rfl

/-- Concatenation preserves the same annotated scopes, independently of how
the prefix is grouped. Only the existing Scope associativity is transported. -/
theorem append_assoc {a : ReturnHints first} {b : ReturnHints second} {c : ReturnHints third} :
    HEq ((a.append b).append c) (a.append (b.append c)) := by
  induction a with
  | nil => rfl
  | plain rest ih => exact congr_hints (scope_append_assoc _ _ _) ih (fun x => .plain x)
  | handler rest ih => exact congr_hints (scope_append_assoc _ _ _) ih (fun x => .handler x)
  | cell rest ih => exact congr_hints (scope_append_assoc _ _ _) ih (fun x => .cell x)
  | cleanup rest ih => exact congr_hints (scope_append_assoc _ _ _) ih (fun x => .cleanup x)
  | running kind rest ih => exact congr_hints (scope_append_assoc _ _ _) ih (fun x => .running kind x)
  | live saved rest ihSaved ihRest => exact congr_hints (scope_append_assoc _ _ _) ihRest (fun x => .live saved x)
  | spent rest ih => exact congr_hints (scope_append_assoc _ _ _) ih (fun x => .spent x)

theorem split_scope {first second : SourceDependencyCapture.Scope}
    (hints : ReturnHints (first.append second)) :
    ∃ firstHints : ReturnHints first, ∃ secondHints : ReturnHints second,
      hints = firstHints.append secondHints := by
  induction first with
  | nil => exact ⟨.nil, hints, rfl⟩
  | plain dependencies rest ih => cases hints with | plain tail =>
      obtain ⟨a, b, rfl⟩ := ih tail
      exact ⟨.plain a, b, rfl⟩
  | handler effect table families rest ih => cases hints with | handler tail =>
      obtain ⟨a, b, rfl⟩ := ih tail
      exact ⟨.handler a, b, rfl⟩
  | cell identity rest ih => cases hints with | cell tail =>
      obtain ⟨a, b, rfl⟩ := ih tail
      exact ⟨.cell a, b, rfl⟩
  | cleanup needs dependencies rest ih => cases hints with | cleanup tail =>
      obtain ⟨a, b, rfl⟩ := ih tail
      exact ⟨.cleanup a, b, rfl⟩
  | running rest ih => cases hints with | running kind tail =>
      obtain ⟨a, b, rfl⟩ := ih tail
      exact ⟨.running kind a, b, rfl⟩
  | live owner captured rest ihSaved ihRest => cases hints with | live inside tail =>
      obtain ⟨a, b, rfl⟩ := ihRest tail
      exact ⟨.live inside a, b, rfl⟩
  | spent owner rest ih => cases hints with | spent tail =>
      obtain ⟨a, b, rfl⟩ := ih tail
      exact ⟨.spent a, b, rfl⟩

end Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.append_assoc
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.split_scope

namespace Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive
open SourceDependencyCapture (Scope)
open LexicalUnwind (UseMode)

/-- Transport only equality of the annotated source, not a semantic change. -/
theorem Local.reindex_scope {hints : ReturnHints scope} {next : ReturnHints nextScope}
    (checked : Local outward actions phases world dependencies hints)
    (same : scope = nextScope) (related : HEq hints next) :
    Local outward actions phases world dependencies next := by
  cases same
  cases eq_of_heq related
  exact checked

theorem Pending.reindex_outside {outside : ReturnHints outsideScope} {next : ReturnHints nextScope}
    (checked : Pending outward actions phases world hints outside before after)
    (same : outsideScope = nextScope) (related : HEq outside next) :
    Pending outward actions phases world hints next before after := by
  cases same
  cases eq_of_heq related
  exact checked

/-- Splitting an annotated prefix preserves the exact receiving suffix for
all executed code and callbacks, including dormant and opening captures. -/
theorem Pending.split {first : ReturnHints firstScope} {second : ReturnHints secondScope}
    {outside : ReturnHints outsideScope}
    (checked : Pending outward actions phases world (first.append second) outside before after) :
    ∃ middle, Pending outward actions phases world first (second.append outside) before middle ∧
      Pending outward actions phases world second outside middle after := by
  induction first generalizing outsideScope before after with
  | nil => exact ⟨before, .nil, checked⟩
  | plain rest ih => cases checked with
    | plain code tail =>
        obtain ⟨middle, inside, remaining⟩ := ih tail
        exact ⟨middle, .plain (code.reindex_scope (scope_append_assoc _ _ _) ReturnHints.append_assoc) inside, remaining⟩
    | skipped tail =>
        obtain ⟨middle, inside, remaining⟩ := ih tail
        exact ⟨middle, .skipped inside, remaining⟩
  | handler rest ih => cases checked with | handler tail =>
      obtain ⟨middle, inside, remaining⟩ := ih tail
      exact ⟨middle, .handler inside, remaining⟩
  | cell rest ih => cases checked with | cell tail =>
      obtain ⟨middle, inside, remaining⟩ := ih tail
      exact ⟨middle, .cell inside, remaining⟩
  | cleanup rest ih => cases checked with | cleanup callback tail =>
      obtain ⟨middle, inside, remaining⟩ := ih tail
      exact ⟨middle, .cleanup
        (callback.reindex_scope (congrArg Scope.running (scope_append_assoc _ _ _))
          (congr_hints (scope_append_assoc _ _ _) ReturnHints.append_assoc (fun x => .running (callbackBoundary before) x))) inside,
        remaining⟩
  | running kind rest ih => cases checked with
    | normal tail =>
        obtain ⟨middle, inside, remaining⟩ := ih tail
        exact ⟨middle, .normal inside, remaining⟩
    | unwinding tail =>
        obtain ⟨middle, inside, remaining⟩ := ih tail
        exact ⟨middle, .unwinding inside, remaining⟩
    | closing tail =>
        obtain ⟨middle, inside, remaining⟩ := ih tail
        exact ⟨middle, .closing inside, remaining⟩
    | retiring tail =>
        obtain ⟨middle, inside, remaining⟩ := ih tail
        exact ⟨middle, .retiring inside, remaining⟩
  | live saved rest ihSaved ihRest => cases checked with
    | live inside tail =>
        obtain ⟨middle, first, remaining⟩ := ihRest tail
        exact ⟨middle, .live (inside.reindex_outside (scope_append_assoc _ _ _) ReturnHints.append_assoc) first, remaining⟩
    | opening inside tail =>
        obtain ⟨middle, first, remaining⟩ := ihRest tail
        exact ⟨middle, .opening
          (inside.reindex_outside (congrArg Scope.running (scope_append_assoc _ _ _))
            (congr_hints (scope_append_assoc _ _ _) ReturnHints.append_assoc (fun x => .running .retire x))) first,
          remaining⟩
  | spent rest ih => cases checked with | spent tail =>
      obtain ⟨middle, inside, remaining⟩ := ih tail
      exact ⟨middle, .spent inside, remaining⟩

/-- The existing physical handler cut determines the annotated split. All
recursive checks refer to that same capture and waiting suffix. -/
theorem Pending.handler_cut {handler : ScopedExecution.HandlerData} {hints : ReturnHints scope}
    (checked : Pending outward actions phases world hints .nil .ordinary finalMode)
    (matching : Matches tables families hints whole)
    (cut : ScopedExecution.HandlerCut requested whole captured tail handler) :
    ∃ capturedScope tailScope, ∃ capturedHints : ReturnHints capturedScope,
    ∃ tailHints : ReturnHints tailScope, ∃ middle,
      scope = capturedScope.append tailScope ∧ HEq hints (capturedHints.append tailHints) ∧
      Matches tables families capturedHints captured ∧ Matches tables families tailHints tail ∧
      Pending outward actions phases world capturedHints (tailHints.append .nil) .ordinary middle ∧
      Pending outward actions phases world tailHints .nil middle finalMode := by
  obtain ⟨capturedScope, tailScope, inside, outside, same, selection⟩ := matching.erases.cut cut
  cases same
  obtain ⟨capturedHints, tailHints, rfl⟩ := ReturnHints.split_scope hints
  rw [ScopedExecution.handler_cut_reconstructs cut] at matching
  obtain ⟨savedMatch, tailMatch⟩ := matching.split_at inside
  obtain ⟨middle, savedCheck, tailCheck⟩ := checked.split
  exact ⟨_, _, _, _, middle, rfl, HEq.rfl, savedMatch, tailMatch, savedCheck, tailCheck⟩

end Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local.reindex_scope
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive.Pending.reindex_outside
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive.Pending.split
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive.Pending.handler_cut

namespace Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive
open ScopedExpressions ScopedExecution SourceDependencyAnnotations

/-- Rich source identifies the requested effect; recursive sequencing exposes
its local request check without an independent request-admission premise. -/
theorem Local.ready_request
    (current : Expression operations policy contracts world allowed runtimeScope environment
      (.perform (Instantiation.freezeEffect requested) operation value) result demand requirements dependencies)
    (checked : Local outward actions phases world dependencies hints) :
    Local outward actions phases world (.request requested operation) hints := by
  generalize encoded : Instantiation.freezeEffect requested = actual at current
  cases current with | perform known admitted operand formed =>
    cases freeze_effect_injective encoded
    cases checked with | sequence first second => exact second

theorem Local.request_guard {hints : ReturnHints scope}
    (checked : Local outward actions phases world (.request effect operation) hints) :
    Lexical.Capture scope effect operation := by
  cases checked with | request guard callbacks owners => exact guard

end Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local.ready_request
#print axioms Ash.OneShot.SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local.request_guard
