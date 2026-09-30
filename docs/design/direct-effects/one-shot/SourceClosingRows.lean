import SourceTemplates

/-! Closing-plan rows retain shared callable source evidence. The plan order and
    residual equations are unchanged from SharedClosingSource. -/
namespace Ash.OneShot.SourceClosingRows
open ScopedExpressions ScopedExecution ProtectionContracts CoherentSourceTypes
open Owners (Contracts)

inductive Contents (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts) (world : List Nat) : List CloseEntry → Prop where
  | nil : Contents operations policy contracts world []
  | release (rest : Contents operations policy contracts world tail) : Contents operations policy contracts world (.release identity payload :: tail)
  | retire (known : contracts owner = some contract) (rest : Contents operations policy contracts world tail) :
      Contents operations policy contracts world (.retire owner :: tail)
  | invoke (callback : SourceTemplates.ValueSummary operations policy contracts world Environment.empty [] action.action (.function .unit .unit action.requests latent))
      (rest : Contents operations policy contracts world tail) : Contents operations policy contracts world (.invoke action :: tail)

theorem contents_append (first : Contents operations policy contracts world before) (second : Contents operations policy contracts world after) :
    Contents operations policy contracts world (before ++ after) := by
  induction first with
  | nil => exact second
  | release rest ih => exact .release ih
  | retire known rest ih => exact .retire known ih
  | invoke callback rest ih => exact .invoke callback ih

inductive Rows (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts) (world : List Nat) : List CloseEntry → Footprint → Prop where
  | nil : Rows operations policy contracts world [] []
  | release (rest : Rows operations policy contracts world tail row) : Rows operations policy contracts world (.release identity payload :: tail) row
  | retire (known : contracts owner = some contract) (rest : Rows operations policy contracts world tail row) :
      Rows operations policy contracts world (.retire owner :: tail) row
  | invoke (callback : SourceTemplates.ValueSummary operations policy contracts world Environment.empty [] action.action (.function .unit .unit action.requests latent))
      (rest : Rows operations policy contracts world tail row) :
      Rows operations policy contracts world (.invoke action :: tail) (DisposalProtection.callbackResidual tail latent ++ row)

theorem contents_rows (contents : Contents operations policy contracts world plan) : ∃ row, Rows operations policy contracts world plan row := by
  induction contents with
  | nil => exact ⟨[], .nil⟩
  | release rest ih => obtain ⟨row, rows⟩ := ih; exact ⟨row, .release rows⟩
  | retire known rest ih => obtain ⟨row, rows⟩ := ih; exact ⟨row, .retire known rows⟩
  | invoke callback rest ih => obtain ⟨row, rows⟩ := ih; exact ⟨_, .invoke callback rows⟩

theorem from_legacy (source : SharedClosingSource.Rows operations contracts world plan row) :
    Rows operations policy contracts world plan row := by
  induction source with
  | nil => exact .nil
  | release rest ih => exact .release ih
  | retire known rest ih => exact .retire known ih
  | invoke callback rest ih => exact .invoke (.stable callback) ih

end Ash.OneShot.SourceClosingRows
#print axioms Ash.OneShot.SourceClosingRows.contents_append
#print axioms Ash.OneShot.SourceClosingRows.contents_rows
#print axioms Ash.OneShot.SourceClosingRows.from_legacy
