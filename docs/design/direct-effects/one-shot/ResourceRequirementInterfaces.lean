import CoreCallableResourceRequirementClosing

namespace Ash.OneShot.ResourceRequirementInterfaces
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements Key)
open CoreCallableResourceRequirementChecks (Error)
open CoreCallableResourceRequirementClosing (close combine)

/-- Every exact invocation key, callee demand and nearer owner context is retained. -/
theorem invocation_exact (world : List Nat) (key : Key) (demand : List Nat)
    (nearer : OwnerPhases.Context) :
    (close world (.invoke key demand nearer)).map Subtype.val =
      .ok (.invoke key demand nearer) := rfl

theorem retire_unsupported (world : List Nat) (owner : Nat) :
    close world (.retire owner) = .error (.unsupportedRetire owner) := rfl

theorem spent_unsupported (world : List Nat) (owner : Nat) :
    close world (.spent owner) = .error (.unsupportedSpent owner) := rfl

theorem live_request_unsupported (world : List Nat) (owner : Nat) (held : Bool)
    (rest : OwnerPhases.Context) (raw : Footprint) :
    close world (.request (.live owner held :: rest) raw) =
      .error .unsupportedOwnerContext := rfl

theorem spent_request_unsupported (world : List Nat) (owner : Nat)
    (rest : OwnerPhases.Context) (raw : Footprint) :
    close world (.request (.spent owner :: rest) raw) =
      .error .unsupportedOwnerContext := rfl

theorem unissued_cell_rejected (world : List Nat) (identity operation : Nat)
    (fresh : identity ∉ world) :
    close world (.request [] [⟨.cell identity, operation, false⟩]) =
      .error .unissuedCell := by
  dsimp [close, CoreCallableResourceRequirementChecks.interpret,
    CoreCallableResourceRequirementChecks.ordinary, Bind.bind, Except.bind,
    Functor.map, Except.map, ProtectionResiduals.residualize]
  simp [ResourceRequirements.cellNames, CoreCallableGraphAnnotationChecks.subsetB, fresh]

theorem live_emit_unsupported (world : List Nat) (owner : Nat) (held : Bool)
    (rest : OwnerPhases.Context) (raw : Footprint) :
    close world (.emitAfter (.request [] []) (.live owner held :: rest) raw) =
      .error .unsupportedOwnerContext := rfl

theorem spent_emit_unsupported (world : List Nat) (owner : Nat)
    (rest : OwnerPhases.Context) (raw : Footprint) :
    close world (.emitAfter (.request [] []) (.spent owner :: rest) raw) =
      .error .unsupportedOwnerContext := rfl

/-- The output branch term uses the caller's exact permutation, without replacement. -/
theorem choice_output_exact (world : List Nat) (same : a.Perm b)
    (first : Requirements a) (second : Requirements b) :
    (close world (.choice first second same)).map Subtype.val = (do
      let left ← close world first
      let right ← close world second
      .ok (.choice left.val right.val same)) := by
  cases left : close world first <;> cases right : close world second <;>
    simp only [close, left, right, Bind.bind, Except.bind, Except.map, Pure.pure, Except.pure]

/-- Nonempty invocation demands remain in the aggregate resource field. -/
theorem combined_hidden_field {world : List Nat} (key : Key) (callee : List Nat)
    (nearer : OwnerPhases.Context) (needs : CoreCallableCompositionalResourceBody.Need)
    (closed : { outward : Requirements ((key.owner :: callee) ++ []) //
      ∀ identity, identity ∉ world → ResourceRequirements.Hides identity
        (.sequence (.invoke key callee nearer) (needs.requirements identity)) outward })
    (fresh : identity ∉ world) :
    ResourceRequirements.Hides identity
      (.sequence (.invoke key callee nearer) (needs.requirements identity)) closed.val :=
  closed.property identity fresh

/-- A successful computed result directly supplies the existing all-fresh field. -/
theorem resource_hidden_field
    (closed : CoreCallableResourceRequirementClosing.Closed world opened)
    (fresh : identity ∉ world) :
    ResourceRequirements.Hides identity opened closed.val := closed.property identity fresh

/-- Both branch demand indices and the actual permutation occur in the original fold. -/
theorem choice_hidden_field (same : a.Perm b) (first : Requirements a)
    (second : Requirements b)
    (closed : CoreCallableResourceRequirementClosing.Closed world (.choice first second same))
    (fresh : identity ∉ world) :
    ResourceRequirements.Hides identity (.choice first second same) closed.val :=
  closed.property identity fresh

end Ash.OneShot.ResourceRequirementInterfaces

#check Ash.OneShot.CoreCallableResourceRequirementChecks.ordinary
#check Ash.OneShot.CoreCallableResourceRequirementChecks.interpret
#check Ash.OneShot.CoreCallableResourceRequirementClosing.Closed
#check Ash.OneShot.CoreCallableResourceRequirementClosing.close
#check Ash.OneShot.CoreCallableResourceRequirementClosing.combine
#check Ash.OneShot.ResourceRequirementInterfaces.invocation_exact
#check Ash.OneShot.ResourceRequirementInterfaces.resource_hidden_field
#check Ash.OneShot.ResourceRequirementInterfaces.choice_hidden_field
#check Ash.OneShot.ResourceRequirementInterfaces.combined_hidden_field
#check Ash.OneShot.ResourceRequirementInterfaces.choice_output_exact
#print axioms Ash.OneShot.ResourceRequirementInterfaces.invocation_exact
#print axioms Ash.OneShot.ResourceRequirementInterfaces.retire_unsupported
#print axioms Ash.OneShot.ResourceRequirementInterfaces.spent_unsupported
#print axioms Ash.OneShot.ResourceRequirementInterfaces.live_request_unsupported
#print axioms Ash.OneShot.ResourceRequirementInterfaces.spent_request_unsupported
#print axioms Ash.OneShot.ResourceRequirementInterfaces.unissued_cell_rejected
#print axioms Ash.OneShot.ResourceRequirementInterfaces.live_emit_unsupported
#print axioms Ash.OneShot.ResourceRequirementInterfaces.spent_emit_unsupported
#print axioms Ash.OneShot.ResourceRequirementInterfaces.choice_output_exact
#print axioms Ash.OneShot.ResourceRequirementInterfaces.combined_hidden_field
#print axioms Ash.OneShot.ResourceRequirementInterfaces.resource_hidden_field
#print axioms Ash.OneShot.ResourceRequirementInterfaces.choice_hidden_field
