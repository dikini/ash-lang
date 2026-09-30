import SourceScheduledBypassedRechecking
import SourceScheduledSourceRecheckingExamples

/-! Source-derived bypass checks retain effectful callbacks and callbacks that
invoke another live owner. The insertion position determines interference. -/
namespace Ash.OneShot.SourceScheduledSourceRechecking.BypassedExamples
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Code recipeLaws)
open SourceDependencyCapture.Examples (resumeTable resumeDependencies disposeTable disposeDependencies effectE)

namespace Shielded
open SourceConsumingHandlerInterference.Examples

def front := armed.append (Forest.cell (identity := 4) .nil)
def outside : Forest (Hints.handler (effect := disposingEffect) (table := disposeTable)
    (families := disposeDependencies) [] .nil) := .handler .nil
def target := front.append (Forest.handler (effect := callbackEffect) (table := resumeTable)
  (families := resumeDependencies) (required := []) outside)

/-- The callback and new handler share an effect. Its original builtin lies
before the insertion, so the source-derived boundary bound admits this case. -/
theorem rechecked : Expression [] actions phases oldRequest target :=
  Expression.bypassed_selected_from_bound front (by decide) (by decide) (.hit rfl rfl)
    source_valid.1 (by decide)

theorem generated : ∃ annotation : Code [4] (.request (effect := disposingEffect) (operation := 0)) target,
    annotation.Valid [] actions phases ∧ SourcePlanBounds.ofCode annotation = SourcePlanBounds.ofCode oldRequest :=
  rechecked.compile_retaining (recipeLaws []) (fun evidence => evidence) source_valid.1

def nextReceiver := Forest.cell (identity := 4)
  (Forest.handler (effect := callbackEffect) (table := resumeTable)
    (families := resumeDependencies) (required := []) outside)

/-- Integrate the derived request rule with the whole saved source. The
callback's primitive operation check still resolves to the original builtin. -/
theorem saved_rechecked : ReceiverChange [] actions phases source nextReceiver :=
  .plain rechecked (.cleanup (.operations rfl) (.handler rfl .empty))

theorem saved_generated : ∃ annotation : SourceScheduledCapabilityAnnotations.Retained [4] saved nextReceiver,
    annotation.Valid [] actions phases ∧
    SourceBoundSnapshots.Retained.ofCapability annotation = SourceBoundSnapshots.Retained.ofCapability source :=
  saved_rechecked.compile_retaining (recipeLaws []) (fun evidence => evidence) source_valid

def afterCapture : Forest (Hints.handler (effect := .user 700 []) (table := [])
    (families := []) [] .nil) := .handler .nil
def waitingTarget := (armed.append waiting).append afterCapture

/-- When insertion lies outside the selected capture, recursively check only
its actual closing callback. Selection and owner bounds come from the source. -/
theorem waiting_rechecked : Expression [] actions phases oldRequest waitingTarget :=
  Expression.waiting_selected afterCapture source_valid.1
    (fun _ => .cleanup (.operations rfl) (.cell .empty))

theorem waiting_generated : ∃ annotation : Code [4]
    (.request (effect := disposingEffect) (operation := 0)) waitingTarget,
    annotation.Valid [] actions phases ∧ SourcePlanBounds.ofCode annotation = SourcePlanBounds.ofCode oldRequest :=
  waiting_rechecked.compile_retaining (recipeLaws []) (fun evidence => evidence) source_valid.1

/-- Moving the same handler ahead of the builtin changes the result. Original
capture validity alone cannot justify that insertion. -/
theorem before_provider_rejected : SourceDependencyCapture.checkCapture []
    ((SourceDependencyCapture.Scope.cleanup [callbackEffect] (.request callbackEffect 0)
      (.handler outerEffect resumeTable SourceScheduledClauseHandlers.Examples.innerFamilies .nil)).append
      (.handler callbackEffect resumeTable resumeDependencies
        (.cell 4 (.handler disposingEffect disposeTable disposeDependencies .nil))))
    disposingEffect 0 = false := rfl

end Shielded

namespace InvokingCallback
open SourceScheduledSourceRechecking.Examples

/-- Reuse the already checked original closing transformation, which retains
a callback invoking owner 37 rather than an operation-only footprint. -/
noncomputable def closingSource := Classical.choose
  (rich_closing.compile (recipeLaws []) (fun evidence => evidence) original_valid)

theorem closing_valid : closingSource.Valid [] actions phases := Classical.choose_spec
  (rich_closing.compile (recipeLaws []) (fun evidence => evidence) original_valid)

noncomputable def selected : Code [] (.request (effect := effectE) (operation := 0)) after :=
  .selected intercepted.cut (fun _ => .cleanup (.handler .nil)) (fun _ => closingSource)

theorem selected_valid : selected.Valid [] actions phases := ⟨by decide, fun _ => closing_valid⟩

def outside := Forest.handler (effect := effectE) (table := disposeTable)
  (families := disposeDependencies) (required := []) waiting
def target := front.append (Forest.handler (effect := .user 700 []) (table := [])
  (families := []) (required := []) outside)

/-- Neither a target closing derivation nor target callback validity is
provided. The original closing source is reused after handler erasure. -/
theorem rechecked : Expression [] actions phases selected target :=
  Expression.bypassed_selected_from_bound front (by decide) (by decide) (.hit rfl rfl)
    selected_valid (by decide)

theorem generated : ∃ annotation : Code [] (.request (effect := effectE) (operation := 0)) target,
    annotation.Valid [] actions phases ∧ SourcePlanBounds.ofCode annotation = SourcePlanBounds.ofCode selected :=
  rechecked.compile_retaining (recipeLaws []) (fun evidence => evidence) selected_valid

end InvokingCallback
namespace Capability
open SourceContextualClauses (RequestCapability)
open SourceContextualRequirements (check_capability_iff)

/-- A selected disposer may be reinterpreted by a builtin. The original
request is not an operation-only annotation and its old contract may dispose. -/
def oldCell : Forest (Hints.handler (effect := .cell 4) (table := disposeTable)
    (families := disposeDependencies) [] .nil) := .handler .nil
def cellRequest : Code [4] (.request (effect := .cell 4) (operation := 0)) oldCell :=
  .selected (.hit rfl rfl) (fun _ => .handler .nil) (fun _ => .operations .nil)
def builtin : Forest (Hints.cell (identity := 4) .nil) := .cell .nil

theorem cell_valid : cellRequest.Valid [] (fun _ => none) (OwnerPhaseTransitions.available []) :=
  ⟨rfl, fun _ => rfl⟩

theorem builtin_rechecked : Expression [] (fun _ => none) (OwnerPhaseTransitions.available []) cellRequest builtin :=
  .capability (.builtin rfl)

theorem builtin_generated : ∃ annotation : Code [4]
    (.request (effect := .cell 4) (operation := 0)) builtin,
    annotation.Valid [] (fun _ => none) (OwnerPhaseTransitions.available []) ∧
    SourcePlanBounds.ofCode annotation = SourcePlanBounds.ofCode cellRequest :=
  builtin_rechecked.compile_retaining (recipeLaws []) (fun evidence => evidence) cell_valid

open SourceConsumingHandlerInterference.Examples

def resuming : Forest (Hints.cell (identity := 4)
    (.handler (effect := disposingEffect) (table := resumeTable)
      (families := resumeDependencies) [] .nil)) := .cell (.handler .nil)

/-- Recheck the whole original saved source, including its effectful callback.
The changed request contract no longer needs a disposal closing derivation. -/
theorem saved_rechecked : ReceiverChange [] actions phases source resuming :=
  .plain (.capability (check_capability_iff.mp rfl))
    (.cleanup (.operations rfl) (.handler rfl .empty))

theorem saved_generated : ∃ annotation : SourceScheduledCapabilityAnnotations.Retained [4] saved resuming,
    annotation.Valid [] actions phases ∧
    SourceBoundSnapshots.Retained.ofCapability annotation = SourceBoundSnapshots.Retained.ofCapability source :=
  saved_rechecked.compile_retaining (recipeLaws []) (fun evidence => evidence) source_valid

/-- The same request can be checked in a protected callback. Neither a
continuation permission nor a new owner phase is supplied by this rule. -/
theorem protected_rechecked : Expression [] actions phases oldRequest (.running (armed.append resuming)) :=
  .capability (check_capability_iff.mp rfl)

/-- Missing operations do not fall through a nearer same-effect handler,
even if a builtin provider exists after it. -/
theorem missing_operation_rejected : ¬ RequestCapability (.cell 4) 1
    (.handler (.cell 4) resumeTable resumeDependencies (.cell 4 .nil)) := by
  intro capability
  have checked := check_capability_iff.mpr capability
  change false = true at checked
  cases checked

/-- This rule cannot discharge a disposing target's capture obligations.
Such a target still uses selected/fresh source rules with closing evidence. -/
theorem disposing_capability_rejected : ¬ RequestCapability disposingEffect 0
    (.handler disposingEffect disposeTable disposeDependencies .nil) := by
  intro capability
  have checked := check_capability_iff.mpr capability
  change false = true at checked
  cases checked

/-- Resume-only is insufficient if the selected declaration omits its
protected mode. The independent capability checker requires both modes. -/
theorem missing_protected_mode_rejected : ¬ RequestCapability disposingEffect 0
    (.handler disposingEffect [(0, ⟨false, some [], none⟩)]
      [(0, some SourceDependencyCapture.Examples.resumeFamily, none)] .nil) := by
  intro capability
  have checked := check_capability_iff.mpr capability
  change false = true at checked
  cases checked

end Capability

end Ash.OneShot.SourceScheduledSourceRechecking.BypassedExamples

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.BypassedExamples.Shielded.rechecked
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.BypassedExamples.Shielded.generated
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.BypassedExamples.Shielded.saved_rechecked
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.BypassedExamples.Shielded.saved_generated
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.BypassedExamples.Shielded.waiting_rechecked
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.BypassedExamples.Shielded.waiting_generated
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.BypassedExamples.Shielded.before_provider_rejected
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.BypassedExamples.InvokingCallback.closing_valid
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.BypassedExamples.InvokingCallback.selected_valid
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.BypassedExamples.InvokingCallback.rechecked
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.BypassedExamples.InvokingCallback.generated

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.BypassedExamples.Capability.cell_valid
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.BypassedExamples.Capability.builtin_rechecked
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.BypassedExamples.Capability.builtin_generated
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.BypassedExamples.Capability.saved_rechecked
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.BypassedExamples.Capability.saved_generated
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.BypassedExamples.Capability.protected_rechecked
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.BypassedExamples.Capability.missing_operation_rejected
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.BypassedExamples.Capability.disposing_capability_rejected
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.BypassedExamples.Capability.missing_protected_mode_rejected
