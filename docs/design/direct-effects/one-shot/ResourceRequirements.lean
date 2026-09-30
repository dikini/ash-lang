import RecursiveRequirements

/-!
Structural discharge of local cell requests, retaining recursive continuation
calls. Freshness is derived from each finite successful checking derivation;
the ordered interpreter and invocation checker are unchanged.
-/

namespace Ash.OneShot.ResourceRequirements
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements Checked Store evaluate)
open OwnerPhaseTransitions (Phases spendAll)

def cellNames (row : Footprint) : List Nat := row.filterMap fun request =>
  match request.effect with | .cell identity => some identity | _ => none

theorem outside_fresh (fresh : identity ∉ cellNames row) : CallableProtection.outsideCell identity row = row := by
  apply List.filter_eq_self.mpr
  intro request member
  simp only [bne_iff_ne]
  intro same
  apply fresh
  exact List.mem_filterMap.mpr ⟨request, member, by simp only [same]⟩

theorem ordinary_consume_middle (front receiving : OwnerPhases.Context) (owner : Nat) (layer : Layer) :
    (OwnerPhases.consume owner (front ++ .ordinary layer :: receiving)).isSome =
      (OwnerPhases.consume owner (front ++ receiving)).isSome := by
  induction front with
  | nil => simp [OwnerPhases.consume]
  | cons entry rest ih =>
      cases entry with
      | ordinary next => simpa [OwnerPhases.consume] using ih
      | live other held => by_cases same : owner = other <;> simp [OwnerPhases.consume, same, ih]
      | spent other => by_cases same : owner = other <;> simp [OwnerPhases.consume, same, ih]

theorem selection_insert_builtin
    (selection : OwnerPhases.Consumes owner (front ++ receiving) waiting) :
    ∃ next, OwnerPhases.Consumes owner (front ++ .ordinary (.builtin identity) :: receiving) next := by
  have existsFirst : (OwnerPhases.consume owner (front ++ receiving)).isSome = true := by
    rw [OwnerPhases.consumes_sound selection]; rfl
  rw [← ordinary_consume_middle front receiving owner (.builtin identity)] at existsFirst
  cases found : OwnerPhases.consume owner (front ++ .ordinary (.builtin identity) :: receiving) with
  | none => simp [found] at existsFirst
  | some next => exact ⟨next, OwnerPhases.consumes_complete found⟩

/-- Only the row reaching this precise stack position matters for freshness;
    nearer source interpretations may have expanded the original demands. -/
theorem export_insert_builtin
    (exported : OwnerSource.exportAt (front ++ receiving) before raw = some row) :
    ∃ forbidden : List Nat, ∀ identity, identity ∉ forbidden →
      OwnerSource.exportAt (front ++ .ordinary (.builtin identity) :: receiving) before raw = some row := by
  simp only [OwnerSource.exportAt, OwnerPhaseTransitions.project_append, residual_append] at exported ⊢
  cases prefixRow : residualize (OwnerPhaseTransitions.project front before) raw with
  | none => simp [prefixRow] at exported
  | some exposed =>
      refine ⟨cellNames exposed, ?_⟩
      intro identity fresh
      simpa only [prefixRow, OwnerPhaseTransitions.project, residual_builtin, outside_fresh fresh] using exported

/-- Induction traverses the already authenticated saved bodies, including
    arbitrary finite nesting. It produces a finite allocation exclusion set. -/
theorem checked_insert_builtin
    (checked : Checked store original before requirements row)
    (split : original = front ++ receiving) :
    ∃ forbidden : List Nat, ∀ identity, identity ∉ forbidden →
      Checked store (front ++ .ordinary (.builtin identity) :: receiving) before requirements row := by
  induction checked generalizing front receiving with
  | request exported =>
      obtain ⟨names, preserved⟩ := export_insert_builtin (front := _ ++ front) (receiving := receiving)
        (by simpa only [split, List.append_assoc] using exported)
      exact ⟨names, fun identity fresh => .request (by simpa only [List.append_assoc] using preserved identity fresh)⟩
  | retire ready => exact ⟨[], fun _ _ => .retire ready⟩
  | spent consumed => exact ⟨[], fun _ _ => .spent consumed⟩
  | invoke known ready selection next ih =>
      rename_i key demand body phases nearer current waiting output
      obtain ⟨names, preserved⟩ := ih (front := nearer ++ front) (receiving := receiving)
        (by simp only [split, List.append_assoc])
      refine ⟨names, ?_⟩
      intro identity fresh
      obtain ⟨waiting, selected⟩ := selection_insert_builtin (identity := identity) (front := _ ++ front)
        (receiving := receiving) (by simpa only [split, List.append_assoc] using selection)
      exact .invoke known ready (by simpa only [List.append_assoc] using selected)
        (by simpa only [List.append_assoc] using preserved identity fresh)
  | sequence first second ihFirst ihSecond =>
      obtain ⟨left, leftPreserved⟩ := ihFirst split
      obtain ⟨right, rightPreserved⟩ := ihSecond split
      exact ⟨left ++ right, fun identity fresh => .sequence
        (leftPreserved identity (fun member => fresh (List.mem_append_left _ member)))
        (rightPreserved identity (fun member => fresh (List.mem_append_right _ member)))⟩
  | emitAfter body exported ih =>
      obtain ⟨left, leftPreserved⟩ := ih split
      obtain ⟨right, rightPreserved⟩ := export_insert_builtin (front := _ ++ front) (receiving := receiving)
        (by simpa only [split, List.append_assoc] using exported)
      refine ⟨left ++ right, ?_⟩
      intro identity fresh
      exact .emitAfter (leftPreserved identity (fun member => fresh (List.mem_append_left _ member)))
        (by simpa only [List.append_assoc] using rightPreserved identity (fun member => fresh (List.mem_append_right _ member)))
  | choice first second ihFirst ihSecond =>
      obtain ⟨left, leftPreserved⟩ := ihFirst split
      obtain ⟨right, rightPreserved⟩ := ihSecond split
      exact ⟨left ++ right, fun identity fresh => .choice
        (leftPreserved identity (fun member => fresh (List.mem_append_left _ member)))
        (rightPreserved identity (fun member => fresh (List.mem_append_right _ member)))⟩

/-- Discharge removes local requests after their nearer interpretations.
    Invocation contexts, sequencing and branch demands are retained. -/
inductive Hides (identity : Nat) : {owners : List Nat} → Requirements owners → Requirements owners → Prop where
  | request : Hides identity (.request [] raw) (.request [] (CallableProtection.outsideCell identity raw))
  | requestThrough (exported : residualize layers raw = some interpreted) :
      Hides identity (.request (layers.map OwnerPhases.Entry.ordinary) raw)
        (.request [] (CallableProtection.outsideCell identity interpreted))
  | invoke : Hides identity (.invoke key demand nearer) (.invoke key demand nearer)
  | sequence (first : Hides identity a x) (second : Hides identity b y) :
      Hides identity (.sequence a b) (.sequence x y)
  | emitAfter (body : Hides identity a b) :
      Hides identity (.emitAfter a [] raw) (.emitAfter b [] (CallableProtection.outsideCell identity raw))
  | emitThrough (body : Hides identity a b) (exported : residualize layers raw = some interpreted) :
      Hides identity (.emitAfter a (layers.map OwnerPhases.Entry.ordinary) raw)
        (.emitAfter b [] (CallableProtection.outsideCell identity interpreted))
  | choice (first : Hides identity a x) (second : Hides identity b y) :
      Hides identity (.choice a b same) (.choice x y same)

theorem outside_idempotent (identity : Nat) (row : Footprint) :
    CallableProtection.outsideCell identity (CallableProtection.outsideCell identity row) =
      CallableProtection.outsideCell identity row := by
  simp [CallableProtection.outsideCell, List.filter_filter]

theorem ordinary_project (layers : ProtectionContracts.Context) (before : OwnerPhaseTransitions.Phases) :
    OwnerPhaseTransitions.project (layers.map OwnerPhases.Entry.ordinary) before = layers := by
  induction layers <;> simp_all [OwnerPhaseTransitions.project]

/-- Interpret nearer source handlers before discharging the local builtin.
    The emitted row may introduce local requests or export formerly local ones. -/
theorem export_hidden_after_interpretation
    (exported : residualize layers raw = some interpreted) :
    OwnerSource.exportAt (layers.map OwnerPhases.Entry.ordinary ++ .ordinary (.builtin identity) :: receiving) before raw =
      OwnerSource.exportAt (.ordinary (.builtin identity) :: receiving) before
        (CallableProtection.outsideCell identity interpreted) := by
  simp only [OwnerSource.exportAt, OwnerPhaseTransitions.project_append, ordinary_project,
    residual_append, exported, OwnerPhaseTransitions.project, residual_builtin, outside_idempotent]

theorem evaluate_hidden (hidden : Hides identity opened closed) :
    evaluate store (.ordinary (.builtin identity) :: receiving) before opened =
      evaluate store (.ordinary (.builtin identity) :: receiving) before closed := by
  induction hidden generalizing before with
  | request =>
      simp only [evaluate, RecursiveRequirements.evaluateFuel, List.nil_append, OwnerSource.exportAt,
        OwnerPhaseTransitions.project, residual_builtin, outside_idempotent]
  | requestThrough exported =>
      simpa only [evaluate, RecursiveRequirements.evaluateFuel, List.nil_append] using
        export_hidden_after_interpretation (receiving := receiving) (before := before) (identity := identity) exported
  | invoke => rfl
  | sequence first second ihFirst ihSecond => simp only [RecursiveRequirements.evaluate_sequence, ihFirst, ihSecond]
  | emitAfter body ih =>
      simp only [RecursiveRequirements.evaluate_emit, ih, List.nil_append, OwnerSource.exportAt,
        OwnerPhaseTransitions.project, residual_builtin, outside_idempotent]
  | emitThrough body exported ih =>
      simp only [RecursiveRequirements.evaluate_emit, ih, List.nil_append,
        export_hidden_after_interpretation (identity := identity) exported]
  | choice first second ihFirst ihSecond => simp only [RecursiveRequirements.evaluate_choice, ihFirst, ihSecond]

theorem checked_open_resource
    (checked : Checked store receiving before closed row) :
    ∃ forbidden : List Nat, ∀ identity, identity ∉ forbidden →
      ∀ opened, Hides identity opened closed →
        Checked store (.ordinary (.builtin identity) :: receiving) before opened row := by
  obtain ⟨names, preserved⟩ := checked_insert_builtin checked (front := []) (receiving := receiving) rfl
  refine ⟨names, ?_⟩
  intro identity fresh opened hidden
  apply RecursiveRequirements.evaluate_sound
  rw [evaluate_hidden hidden]
  exact RecursiveRequirements.checked_complete (preserved identity fresh)

namespace Examples

def resumedRequest : Requirements [] := .request [] [⟨.cell 7, 0, false⟩]
def records : Store := [(⟨5, .resume⟩, ⟨[], resumedRequest⟩)]
def invocation : Requirements [5] := .invoke ⟨5, .resume⟩ [] []
def caller : OwnerPhases.Context := [.live 5 false]

/-- Reusing a name observed by the saved body changes its residual. A distinct
    cell leaves that invocation's demand and residual unchanged. -/
theorem allocation_freshness_matters :
    evaluate records caller (OwnerPhaseTransitions.available [5]) invocation = some [⟨.cell 7, 0, false⟩] ∧
    evaluate records (.ordinary (.builtin 7) :: caller) (OwnerPhaseTransitions.available [5]) invocation = some [] ∧
    evaluate records (.ordinary (.builtin 8) :: caller) (OwnerPhaseTransitions.available [5]) invocation = some [⟨.cell 7, 0, false⟩] := by
  simp [records, caller, invocation, resumedRequest, evaluate, RecursiveRequirements.evaluateFuel,
    RecursiveRequirements.lookup, PhaseRechecking.checkOwners, OwnerPhaseTransitions.available,
    OwnerPhaseTransitions.spend, OwnerPhases.consume, OwnerSource.exportAt, OwnerPhaseTransitions.project,
    residualize, throughLayer, demandThrough, merge]

def exportedUser : Footprint := [⟨.user 91 [], 0, false⟩]
def localCell : Footprint := [⟨.cell 7, 0, false⟩]
def overrideLocal : ProtectionContracts.Context := [.handler (.cell 7) 0 [(0, ⟨false, some exportedUser, some exportedUser⟩)]]
def generateLocal : ProtectionContracts.Context := [.handler (.user 91 []) 0 [(0, ⟨false, some localCell, some localCell⟩)]]

/-- A nearer handler exports a local request; early builtin erasure loses it. -/
theorem nearer_handler_exports_local :
    Hides 7 (.request (overrideLocal.map OwnerPhases.Entry.ordinary) localCell) (.request [] exportedUser) ∧
    evaluate [] [.ordinary (.builtin 7)] OwnerPhaseTransitions.empty
      (.request (overrideLocal.map OwnerPhases.Entry.ordinary) localCell) = some exportedUser ∧
    evaluate [] [.ordinary (.builtin 7)] OwnerPhaseTransitions.empty
      (.request (overrideLocal.map OwnerPhases.Entry.ordinary) (CallableProtection.outsideCell 7 localCell)) = some [] := by
  refine ⟨Hides.requestThrough (layers := overrideLocal) (raw := localCell) (interpreted := exportedUser) (by decide), ?_, ?_⟩
  all_goals simp [evaluate, RecursiveRequirements.evaluateFuel, OwnerSource.exportAt, OwnerPhaseTransitions.project,
    overrideLocal, localCell, exportedUser, residualize, throughLayer, demandThrough, lookup, modeCheck,
    ClauseContract.row, merge, CallableProtection.outsideCell]

/-- A nearer handler can instead introduce the request discharged by the cell. -/
theorem nearer_handler_introduces_local :
    Hides 7 (.request (generateLocal.map OwnerPhases.Entry.ordinary) exportedUser) (.request [] []) ∧
    evaluate [] [.ordinary (.builtin 7)] OwnerPhaseTransitions.empty
      (.request (generateLocal.map OwnerPhases.Entry.ordinary) exportedUser) = some [] := by
  refine ⟨Hides.requestThrough (layers := generateLocal) (raw := exportedUser) (interpreted := localCell) (by decide), ?_⟩
  simp [evaluate, RecursiveRequirements.evaluateFuel, OwnerSource.exportAt, OwnerPhaseTransitions.project,
    generateLocal, localCell, exportedUser, residualize, throughLayer, demandThrough, lookup, modeCheck,
    ClauseContract.row, merge]

end Examples

end Ash.OneShot.ResourceRequirements

#print axioms Ash.OneShot.ResourceRequirements.outside_fresh
#print axioms Ash.OneShot.ResourceRequirements.ordinary_consume_middle
#print axioms Ash.OneShot.ResourceRequirements.selection_insert_builtin
#print axioms Ash.OneShot.ResourceRequirements.export_insert_builtin
#print axioms Ash.OneShot.ResourceRequirements.checked_insert_builtin
#print axioms Ash.OneShot.ResourceRequirements.checked_open_resource

#print axioms Ash.OneShot.ResourceRequirements.outside_idempotent
#print axioms Ash.OneShot.ResourceRequirements.evaluate_hidden
#print axioms Ash.OneShot.ResourceRequirements.Examples.allocation_freshness_matters

#print axioms Ash.OneShot.ResourceRequirements.ordinary_project
#print axioms Ash.OneShot.ResourceRequirements.export_hidden_after_interpretation

#print axioms Ash.OneShot.ResourceRequirements.Examples.nearer_handler_exports_local
#print axioms Ash.OneShot.ResourceRequirements.Examples.nearer_handler_introduces_local
