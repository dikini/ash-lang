import ResourceRequirements

/-!
Outward rows for source expressions without an enclosing continuation. The
existing recursive evaluator factors through the expression's own ordered
interpretations and then the receiving context. This is analysis of Code,
not a computation type or a new execution relation.
-/

namespace Ash.OneShot.RecursiveOutward
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements Checked evaluate)
open OwnerPhaseTransitions (Phases spendAll project)

/-- No invocation or owner-phase test occurs in this structural row derivation.
    Missing rows retain failure inside an expression's own interpretations. -/
inductive Outward : {owners : List Nat} → Requirements owners → Option Footprint → Prop where
  | request : Outward (.request (layers.map OwnerPhases.Entry.ordinary) raw) (residualize layers raw)
  | sequence (first : Outward a left) (second : Outward b right) :
      Outward (.sequence a b) (merge left right)
  | emitAfter (body : Outward a row) :
      Outward (.emitAfter a (layers.map OwnerPhases.Entry.ordinary) raw) (merge row (residualize layers raw))
  | choice (first : Outward a left) (second : Outward b right) :
      Outward (.choice a b same) (merge left right)

theorem no_owners (source : Outward (owners := owners) requirements row) : owners = [] := by
  induction source with
  | request => rfl
  | sequence first second ihFirst ihSecond => simp only [ihFirst, ihSecond, List.nil_append]
  | emitAfter body ih => exact ih
  | choice first second ihFirst ihSecond => exact ihFirst

theorem phases_unchanged (source : Outward (owners := owners) requirements row) (before : Phases) :
    spendAll before owners = before := by rw [no_owners source]; rfl

theorem residual_merge (context : ProtectionContracts.Context) (first second : Option Footprint) :
    merge (first.bind (residualize context)) (second.bind (residualize context)) =
      (merge first second).bind (residualize context) := by
  cases first <;> cases second <;> simp [merge, residual_rows_append]

theorem residual_composition (front tail : ProtectionContracts.Context) (row : Option Footprint) :
    (row.bind (residualize front)).bind (residualize tail) = row.bind (residualize (front ++ tail)) := by
  cases row with
  | none => rfl
  | some raw => simp only [Option.bind_some, residual_append]; cases residualize front raw <;> rfl

theorem ordinary_export (layers : ProtectionContracts.Context) (receiving : OwnerPhases.Context)
    (before : Phases) (raw : Footprint) :
    OwnerSource.exportAt (layers.map OwnerPhases.Entry.ordinary ++ receiving) before raw =
      (residualize layers raw).bind (residualize (project receiving before)) := by
  simp only [OwnerSource.exportAt, OwnerPhaseTransitions.project_append, ResourceRequirements.ordinary_project, residual_append]
  cases residualize layers raw <;> rfl

/-- The caller's current phase projection is applied after the expression's
    local interpretations, and no continuation store is consulted. -/
theorem evaluation (source : Outward requirements row) (store : RecursiveRequirements.Store)
    (receiving : OwnerPhases.Context) (before : Phases) :
    evaluate store receiving before requirements = row.bind (residualize (project receiving before)) := by
  induction source with
  | request => simpa only [evaluate, RecursiveRequirements.evaluateFuel] using ordinary_export _ receiving before _
  | sequence first second ihFirst ihSecond =>
      rw [RecursiveRequirements.evaluate_sequence, phases_unchanged first, ihFirst, ihSecond]
      exact residual_merge _ _ _
  | emitAfter body ih =>
      rw [RecursiveRequirements.evaluate_emit, phases_unchanged body, ih, ordinary_export]
      exact residual_merge _ _ _
  | choice first second ihFirst ihSecond =>
      rw [RecursiveRequirements.evaluate_choice, ihFirst, ihSecond]
      exact residual_merge _ _ _

theorem prepend (source : Outward requirements row) (layers : ProtectionContracts.Context) :
    Outward (requirements.prepend (layers.map OwnerPhases.Entry.ordinary)) (row.bind (residualize layers)) := by
  induction source with
  | @request raw nearer =>
      have same := (residual_composition nearer layers (some raw)).symm
      simp only [Option.bind_some] at same
      simpa only [Requirements.prepend, ← List.map_append, same] using
        (Outward.request (layers := nearer ++ layers) (raw := raw))
  | sequence first second ihFirst ihSecond =>
      simpa only [Requirements.prepend, residual_merge] using Outward.sequence ihFirst ihSecond
  | @emitAfter owners a row raw nearer body ih =>
      have combined := Outward.emitAfter (layers := nearer ++ layers) (raw := raw) ih
      have same := (residual_composition nearer layers (some raw)).symm
      simp only [Option.bind_some] at same
      simpa only [Requirements.prepend, ← List.map_append, same, residual_merge] using combined
  | choice first second ihFirst ihSecond =>
      simpa only [Requirements.prepend, residual_merge] using Outward.choice (same := _) ihFirst ihSecond

/-- Structural inversion of ordinary requirements, independent of the
    demand-list indices of their sequence constructors. -/
def Ordinary : {owners : List Nat} → Requirements owners → Prop
  | _, .request nearer _ => ∃ layers : ProtectionContracts.Context, nearer = layers.map OwnerPhases.Entry.ordinary
  | _, .retire _ | _, .spent _ | _, .invoke _ _ _ => False
  | _, .sequence first second | _, .choice first second _ => Ordinary first ∧ Ordinary second
  | _, .emitAfter body nearer _ => Ordinary body ∧ ∃ layers : ProtectionContracts.Context, nearer = layers.map OwnerPhases.Entry.ordinary

theorem ordinary (source : Outward requirements row) : Ordinary requirements := by
  induction source with
  | request => exact ⟨_, rfl⟩
  | sequence first second ihFirst ihSecond | choice first second ihFirst ihSecond => exact ⟨ihFirst, ihSecond⟩
  | emitAfter body ih => exact ⟨ih, _, rfl⟩

theorem ordinary_outward (requirements : Requirements owners) (source : Ordinary requirements) :
    ∃ row, Outward requirements row := by
  induction requirements with
  | request nearer raw => obtain ⟨layers, rfl⟩ := source; exact ⟨_, .request⟩
  | retire | spent | invoke => cases source
  | sequence first second ihFirst ihSecond =>
      obtain ⟨a, left⟩ := ihFirst source.1
      obtain ⟨b, right⟩ := ihSecond source.2
      exact ⟨_, .sequence left right⟩
  | choice first second same ihFirst ihSecond =>
      obtain ⟨a, left⟩ := ihFirst source.1
      obtain ⟨b, right⟩ := ihSecond source.2
      exact ⟨_, .choice left right⟩
  | emitAfter body nearer raw ih =>
      obtain ⟨current, layers, rfl⟩ := source
      obtain ⟨row, checked⟩ := ih current
      exact ⟨_, .emitAfter checked⟩

theorem hidden_ordinary (discharged : ResourceRequirements.Hides identity inside outside)
    (source : Ordinary inside) : Ordinary outside := by
  induction discharged with
  | request | requestThrough => exact ⟨[], rfl⟩
  | invoke => cases source
  | sequence first second ihFirst ihSecond | choice first second ihFirst ihSecond =>
      exact ⟨ihFirst source.1, ihSecond source.2⟩
  | emitAfter body ih => exact ⟨ih source.1, [], rfl⟩
  | emitThrough body exported ih => exact ⟨ih source.1, [], rfl⟩

theorem hidden (discharged : ResourceRequirements.Hides identity inside outside)
    (source : Outward inside row) : ∃ result, Outward outside result :=
  ordinary_outward outside (hidden_ordinary discharged (ordinary source))

end Ash.OneShot.RecursiveOutward

#print axioms Ash.OneShot.RecursiveOutward.no_owners
#print axioms Ash.OneShot.RecursiveOutward.phases_unchanged
#print axioms Ash.OneShot.RecursiveOutward.residual_merge
#print axioms Ash.OneShot.RecursiveOutward.residual_composition
#print axioms Ash.OneShot.RecursiveOutward.ordinary_export
#print axioms Ash.OneShot.RecursiveOutward.evaluation
#print axioms Ash.OneShot.RecursiveOutward.prepend
#print axioms Ash.OneShot.RecursiveOutward.hidden
#print axioms Ash.OneShot.RecursiveOutward.ordinary
#print axioms Ash.OneShot.RecursiveOutward.ordinary_outward
#print axioms Ash.OneShot.RecursiveOutward.hidden_ordinary
