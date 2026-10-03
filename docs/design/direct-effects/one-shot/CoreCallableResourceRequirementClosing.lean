import CoreCallableResourceRequirementChecks
import CoreCallableCompositionalResourceBody

/-! A data-only fold over existing Requirements computes the same-demand outward
requirements and the original resource rule's all-fresh Hides field. It supplies
no body Source, authentication, private Plan, Rows or general resource annotation. -/
namespace Ash.OneShot.CoreCallableResourceRequirementClosing
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements)
open CoreCallableResourceRequirementChecks (Error)

/-- Computed outward requirement at the exact original demand index. -/
abbrev Closed (world : List Nat) (opened : Requirements demand) :=
  { outward : Requirements demand //
    ∀ identity, identity ∉ world → ResourceRequirements.Hides identity opened outward }

private theorem interpreted_hides
    (result : { result : ProtectionContracts.Context × Footprint //
      nearer = result.1.map OwnerPhases.Entry.ordinary ∧
      residualize result.1 raw = some result.2 ∧
      ResourceRequirements.cellNames result.2 ⊆ world })
    (fresh : identity ∉ world) :
    ResourceRequirements.Hides identity (.request nearer raw) (.request [] result.val.2) := by
  rcases result with ⟨⟨layers, row⟩, context, actual, bounded⟩
  have absent : identity ∉ ResourceRequirements.cellNames row :=
    fun member => fresh (bounded member)
  change ResourceRequirements.Hides identity (.request nearer raw) (.request [] row)
  rw [context]
  simpa only [ResourceRequirements.outside_fresh absent] using
    ResourceRequirements.Hides.requestThrough (identity := identity) actual

/-- One recursive fold; no desired output or successful checker result is an input. -/
def close (world : List Nat) : (opened : Requirements demand) → Except Error (Closed world opened)
  | .request nearer raw => do
      let result ← CoreCallableResourceRequirementChecks.interpret world nearer raw
      return ⟨.request [] result.val.2, fun _ fresh => interpreted_hides result fresh⟩
  | .retire owner => .error (.unsupportedRetire owner)
  | .spent owner => .error (.unsupportedSpent owner)
  | .invoke key demand nearer => .ok ⟨.invoke key demand nearer, fun _ _ => .invoke⟩
  | .sequence first second => do
      let left ← close world first
      let right ← close world second
      return ⟨.sequence left.val right.val, fun identity fresh =>
        .sequence (left.property identity fresh) (right.property identity fresh)⟩
  | .emitAfter body nearer raw => do
      let closed ← close world body
      let result ← CoreCallableResourceRequirementChecks.interpret world nearer raw
      return ⟨.emitAfter closed.val [] result.val.2, by
        intro identity fresh
        rcases result with ⟨⟨layers, row⟩, context, actual, bounded⟩
        have absent : identity ∉ ResourceRequirements.cellNames row :=
          fun member => fresh (bounded member)
        change ResourceRequirements.Hides identity
          (.emitAfter body nearer raw) (.emitAfter closed.val [] row)
        rw [context]
        simpa only [ResourceRequirements.outside_fresh absent] using
          ResourceRequirements.Hides.emitThrough (closed.property identity fresh) actual⟩
  | .choice first second same => do
      let left ← close world first
      let right ← close world second
      return ⟨.choice left.val right.val same, fun identity fresh =>
        .choice (left.property identity fresh) (right.property identity fresh)⟩

/-- Attach the existing identity-indexed Need through its original current validator.
The aggregate demand remains demand ++ []; no nil-demand coercion is performed. -/
def combine (original : CoreCallableStaticProducer.Bindings) (binder : Nat)
    (world : List Nat) (residual : List Instance) (opened : Requirements demand)
    (needs : CoreCallableCompositionalResourceBody.Need) :
    Except Error { outward : Requirements (demand ++ []) //
      ∀ identity, identity ∉ world → ResourceRequirements.Hides identity
        (.sequence opened (needs.requirements identity)) outward } := do
  let closed ← close world opened
  if valid : needs.valid original binder world residual = true then
    return ⟨.sequence closed.val needs.outsideRequirements, fun identity fresh =>
      .sequence (closed.property identity fresh) (needs.hides valid fresh)⟩
  else .error .invalidEmbeddedNeed

end Ash.OneShot.CoreCallableResourceRequirementClosing

#print axioms Ash.OneShot.CoreCallableResourceRequirementClosing.close
#print axioms Ash.OneShot.CoreCallableResourceRequirementClosing.combine
