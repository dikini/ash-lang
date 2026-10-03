import ResourceRequirements
import CoreCallableGraphAnnotationChecks

/-! Current finite row interpretation for the existing resource Hides obligation.
Owner phases are retained on invocations. Request and emit interpretation accepts
ordinary layers only; unsupported outcomes do not alter language admission. -/
namespace Ash.OneShot.CoreCallableResourceRequirementChecks
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals

inductive Error where
  | unsupportedOwnerContext
  | unsupportedRetire (owner : Nat)
  | unsupportedSpent (owner : Nat)
  | residualization
  | unissuedCell
  | invalidEmbeddedNeed
  deriving DecidableEq, Repr

/-- Recover the exact existing ordinary layers, without dropping owner entries. -/
def ordinary (nearer : OwnerPhases.Context) :
    Except Error { layers : ProtectionContracts.Context //
      nearer = layers.map OwnerPhases.Entry.ordinary } :=
  match nearer with
  | [] => .ok ⟨[], rfl⟩
  | .ordinary layer :: rest =>
      match ordinary rest with
      | .error error => .error error
      | .ok layers => .ok ⟨layer :: layers.val, by simp only [List.map_cons, layers.property]⟩
  | .live _ _ :: _ | .spent _ :: _ => .error .unsupportedOwnerContext

/-- The row and its ordinary interpretation are computed from current data.
The subset guard excludes each fresh allocation name after interpretation. -/
def interpret (world : List Nat) (nearer : OwnerPhases.Context) (raw : Footprint) :
    Except Error { result : ProtectionContracts.Context × Footprint //
      nearer = result.1.map OwnerPhases.Entry.ordinary ∧
      residualize result.1 raw = some result.2 ∧
      ResourceRequirements.cellNames result.2 ⊆ world } := do
  let layers ← ordinary nearer
  match actual : residualize layers.val raw with
  | none => .error .residualization
  | some row =>
      if issued : CoreCallableGraphAnnotationChecks.subsetB
          (ResourceRequirements.cellNames row) world = true then
        .ok ⟨(layers.val, row), layers.property, actual,
          CoreCallableGraphAnnotationChecks.subsetB_sound issued⟩
      else .error .unissuedCell

end Ash.OneShot.CoreCallableResourceRequirementChecks

#print axioms Ash.OneShot.CoreCallableResourceRequirementChecks.ordinary
#print axioms Ash.OneShot.CoreCallableResourceRequirementChecks.interpret
