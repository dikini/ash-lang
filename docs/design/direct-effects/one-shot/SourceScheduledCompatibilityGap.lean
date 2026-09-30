import SourceScheduledRecipeCapture

/-! Regression for the former loss of handler-requirement evidence. The
strengthened pending judgment rejects a handler requiring an absent provider. -/
namespace Ash.OneShot.SourceScheduledCompatibilityGap
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceScheduledChecks (Pending)
open SourceContextualHintChecking (Compatible)
open SourceDependencyCapture.Examples (effectE effectF)

def hints : Hints (.handler effectE [] [] .nil) := .handler [(effectF, 0)] .nil
def forest : Forest hints := .handler .nil

theorem missing_required_provider_rejected :
    ¬ Pending [] (fun _ => none) (fun _ => .consumed) [] forest .nil := by
  intro checked
  have accepted := (SourceContextualHintChecking.check_iff hints).mpr checked.compatible
  change false = true at accepted
  cases accepted


def providerHints : Hints (SourceDependencyCapture.Examples.handlerF .nil) := .handler [] .nil
def provider : Forest providerHints := .handler .nil

/-- Dormant handler requirements are supplied by the waiting suffix. -/
theorem saved_requirements_supplied :
    Pending [] (fun _ => none) (fun _ => .consumed) []
      (.live (owner := 19) forest provider) .nil :=
  .live (.handler rfl .nil) (.handler rfl .nil)

def maskingHints : Hints (.handler effectF [] [] .nil) := .handler [] .nil
def masking : Forest maskingHints := .handler .nil

/-- Recomposition must check the new caller: its nearer F handler masks the
old provider but lacks the required operation. -/
theorem masking_caller_rejected :
    ¬ Pending [] (fun _ => none) (fun _ => .consumed) []
      forest (masking.append (.spent (owner := 19) provider)) := by
  intro checked
  have accepted := (SourceContextualHintChecking.check_iff hints).mpr checked.compatible
  change false = true at accepted
  cases accepted

end Ash.OneShot.SourceScheduledCompatibilityGap

#print axioms Ash.OneShot.SourceScheduledCompatibilityGap.missing_required_provider_rejected

#print axioms Ash.OneShot.SourceScheduledCompatibilityGap.saved_requirements_supplied
#print axioms Ash.OneShot.SourceScheduledCompatibilityGap.masking_caller_rejected
