import SourceConsumingStoredBounds

/-! Closing control installs no handler packets. Disposal retains the original
caller packets around that exact control. The runtime theorem supplies the
actual plan and disposal permission; this module only transports metadata. -/
namespace Ash.OneShot.SourceConsumingStoredBounds
open SourceAnnotatedRuntime (Stack CloseEntry)

def StackBounds.closing (scope : Execution.Scope) (plan : List CloseEntry) :
    StackBounds families (SourceAnnotatedRuntime.closeControl scope plan) :=
  match plan with
  | [] => .nil
  | .release _ _ :: rest => .push .cell (closing scope rest)
  | .invoke _ :: rest => .push .armed (closing scope rest)
  | .retire _ :: rest => .push .retiring (closing scope rest)

variable {front saved tail : Stack}

def StackBounds.discard
    (source : StackBounds families (front.append (.live owner input answer saved caller tail)))
    (scope : Execution.Scope) (identity : Nat) (plan : List CloseEntry) :
    StackBounds families ((SourceAnnotatedRuntime.closeControl scope plan).append
      (.push (.closing identity scope) (front.append (.spent owner answer caller tail)))) :=
  let pieces := source.splitAt front (.live owner input answer saved caller tail)
  match pieces.2 with
  | .live _ after => (StackBounds.closing scope plan).append (.push .closing (pieces.1.append (.spent after)))

theorem StackBounds.discard_reconstructs
    (source : StackBounds families (front.append (.live owner input answer saved caller tail)))
    (scope : Execution.Scope) (identity : Nat) (plan : List CloseEntry) :
    ∃ before : StackBounds families front, ∃ captured : StackBounds families saved,
    ∃ after : StackBounds families tail,
      before.append (.live captured after) = source ∧
      source.discard scope identity plan =
        (StackBounds.closing scope plan).append (.push .closing (before.append (.spent after))) := by
  have reconstruct := source.splitAt_append front (.live owner input answer saved caller tail)
  unfold StackBounds.discard
  generalize piecesKnown : source.splitAt front (.live owner input answer saved caller tail) = pieces at *
  rcases pieces with ⟨before, remaining⟩
  cases remaining with
  | live captured after => exact ⟨before, captured, after, reconstruct, rfl⟩

section
variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

theorem StackBounds.closing_admitted (scope : Execution.Scope) (plan : List CloseEntry) :
    (StackBounds.closing (families := families) scope plan).Admitted world required := by
  induction plan with
  | nil => exact .nil
  | cons entry rest ih => cases entry with
    | release => exact .push .cell ih
    | invoke => exact .push .armed ih
    | retire => exact .push .retiring ih

theorem StackBounds.Admitted.discard
    {source : StackBounds families (front.append (.live owner input answer saved caller tail))}
    (admitted : source.Admitted world required)
    (scope : Execution.Scope) (identity : Nat) (plan : List CloseEntry) :
    (source.discard scope identity plan).Admitted world required := by
  obtain ⟨before, remaining⟩ := admitted.splitAt front (.live owner input answer saved caller tail)
  unfold StackBounds.discard
  generalize piecesKnown : source.splitAt front (.live owner input answer saved caller tail) = pieces at *
  rcases pieces with ⟨first, second⟩
  cases second with
  | live captured after => cases remaining with
    | live savedChecked tailChecked =>
      exact (StackBounds.closing_admitted scope plan).append (.push .closing (before.append (.spent tailChecked)))

end
end Ash.OneShot.SourceConsumingStoredBounds

#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.discard_reconstructs
#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.closing_admitted
#print axioms Ash.OneShot.SourceConsumingStoredBounds.StackBounds.Admitted.discard
