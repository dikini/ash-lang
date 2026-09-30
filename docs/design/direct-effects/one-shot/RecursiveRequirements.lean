import SharedResumption

/-!
Finite recursive checks for continuation references. An invocation records its
owner and demand rather than a cached row. Its referenced template must have that
exact demand. This is checking data for the existing calculus, not new execution
syntax. General extraction and preserved authentication remain separate work.
-/

namespace Ash.OneShot.RecursiveRequirements
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open OwnerPhaseTransitions (Phases Trace spend spendAll)

inductive Mode where
  | resume | dispose
  deriving DecidableEq, Repr

structure Key where
  owner : Nat
  mode : Mode
  deriving DecidableEq, Repr

inductive Requirements : List Nat → Type where
  | request (nearer : OwnerPhases.Context) (raw : Footprint) : Requirements []
  | retire (owner : Nat) : Requirements [owner]
  | spent (owner : Nat) : Requirements []
  | invoke (key : Key) (demand : List Nat) (nearer : OwnerPhases.Context) : Requirements (key.owner :: demand)
  | sequence (first : Requirements a) (second : Requirements b) : Requirements (a ++ b)
  | emitAfter (body : Requirements demand) (nearer : OwnerPhases.Context) (raw : Footprint) : Requirements demand
  | choice (first : Requirements a) (second : Requirements b) (same : a.Perm b) : Requirements a

def Requirements.size : {owners : List Nat} → Requirements owners → Nat
  | _, .request _ _ | _, .retire _ | _, .spent _ | _, .invoke _ _ _ => 1
  | _, .sequence first second | _, .choice first second _ => first.size + second.size + 1
  | _, .emitAfter body _ _ => body.size + 1

def Requirements.prepend (prefixContext : OwnerPhases.Context) : {owners : List Nat} → Requirements owners → Requirements owners
  | _, .request nearer raw => .request (nearer ++ prefixContext) raw
  | _, .retire owner => .retire owner
  | _, .spent owner => .spent owner
  | _, .invoke key demand nearer => .invoke key demand (nearer ++ prefixContext)
  | _, .sequence first second => .sequence (first.prepend prefixContext) (second.prepend prefixContext)
  | _, .emitAfter body nearer raw => .emitAfter (body.prepend prefixContext) (nearer ++ prefixContext) raw
  | _, .choice first second same => .choice (first.prepend prefixContext) (second.prepend prefixContext) same

abbrev Template := (demand : List Nat) × Requirements demand
abbrev Store := List (Key × Template)

def lookup (key : Key) : Store → Option Template
  | [] => none
  | (candidate, body) :: rest => if key = candidate then some body else lookup key rest

/-- Fuel is bounded below by the demand length in the public checker. It is
    used only across invocation edges; source sequencing does not spend it. -/
def evaluateFuel (fuel : Nat) (store : Store) (receiving : OwnerPhases.Context) (before : Phases)
    {owners : List Nat} (requirements : Requirements owners) : Option Footprint :=
  match requirements with
  | .request nearer raw => OwnerSource.exportAt (nearer ++ receiving) before raw
  | .retire owner => if PhaseRechecking.checkOwners before [owner] then some [] else none
  | .spent owner => if before owner = .consumed then some [] else none
  | .invoke key demand nearer =>
      match fuel with
      | 0 => none
      | next + 1 =>
          match lookup key store with
          | none => none
          | some ⟨actual, body⟩ =>
              if actual = demand ∧ PhaseRechecking.checkOwners before (key.owner :: demand) = true ∧
                (OwnerPhases.consume key.owner (nearer ++ receiving)).isSome = true then
                evaluateFuel next store (nearer ++ receiving) (spend before key.owner) body
              else none
  | @Requirements.sequence a _ first second =>
      merge (evaluateFuel fuel store receiving before first)
        (evaluateFuel fuel store receiving (spendAll before a) second)
  | .emitAfter body nearer raw =>
      merge (evaluateFuel fuel store receiving before body)
        (OwnerSource.exportAt (nearer ++ receiving) (spendAll before owners) raw)
  | .choice first second _ =>
      merge (evaluateFuel fuel store receiving before first) (evaluateFuel fuel store receiving before second)
termination_by (fuel, requirements.size)
decreasing_by
  all_goals simp_wf
  all_goals first
    | apply Prod.Lex.left; omega
    | apply Prod.Lex.right; try simp_all only [Requirements.size]
      all_goals omega

def evaluate (store : Store) (receiving : OwnerPhases.Context) (before : Phases)
    {owners : List Nat} (requirements : Requirements owners) : Option Footprint :=
  evaluateFuel owners.length store receiving before requirements

inductive Calls (key : Key) (demand : List Nat) : {owners : List Nat} → Requirements owners → Prop where
  | here : Calls key demand (.invoke key demand nearer)
  | first (call : Calls key demand first) : Calls key demand (.sequence first second)
  | second (call : Calls key demand second) : Calls key demand (.sequence first second)
  | body (call : Calls key demand body) : Calls key demand (.emitAfter body nearer raw)
  | yes (call : Calls key demand first) : Calls key demand (.choice first second same)
  | no (call : Calls key demand second) : Calls key demand (.choice first second same)

theorem call_decreases (call : Calls key demand (owners := owners) requirements) : demand.length < owners.length := by
  induction call with
  | here => simp
  | first call ih | second call ih => simp only [List.length_append]; omega
  | body call ih | yes call ih => exact ih
  | @no secondOwners second firstOwners first same call ih =>
      rw [same.length_eq]
      exact ih

def rank (store : Store) (key : Key) : Nat := match lookup key store with
  | none => 0
  | some ⟨demand, _⟩ => demand.length

inductive Edge (store : Store) (parent child : Key) : Prop where
  | linked (parentKnown : lookup parent store = some ⟨parentDemand, parentBody⟩)
      (call : Calls child childDemand parentBody)
      (childKnown : lookup child store = some ⟨childDemand, childBody⟩) : Edge store parent child

theorem edge_decreases (edge : Edge store parent child) : rank store child < rank store parent := by
  cases edge with
  | linked parentKnown call childKnown =>
      simp only [rank, parentKnown, childKnown]
      exact call_decreases call

theorem edge_not_self : ¬ Edge store key key := by
  intro edge
  exact Nat.lt_irrefl _ (edge_decreases edge)

theorem path_decreases (path : Relation.TransGen (Edge store) first last) : rank store last < rank store first := by
  induction path with
  | single edge => exact edge_decreases edge
  | tail path edge ih => exact Nat.lt_trans (edge_decreases edge) ih

theorem no_cycle : ¬ Relation.TransGen (Edge store) key key := by
  intro path
  exact Nat.lt_irrefl _ (path_decreases path)

theorem invocation_wellFounded (store : Store) : WellFounded (fun child parent => Edge store parent child) := by
  exact Subrelation.wf (fun edge => edge_decreases edge) (measure (rank store)).wf

theorem fuel_stable_bound (bound : Nat) :
    ∀ {owners} (requirements : Requirements owners), owners.length ≤ bound →
      ∀ first second, owners.length ≤ first → owners.length ≤ second →
        ∀ store receiving before,
          evaluateFuel first store receiving before requirements = evaluateFuel second store receiving before requirements := by
  induction bound using Nat.strongRecOn with
  | ind bound smaller =>
      intro owners requirements
      induction requirements with
      | request | retire | spent => intros; simp only [evaluateFuel]
      | invoke key demand nearer =>
          intro bounded first second enoughFirst enoughSecond store receiving before
          cases first with
          | zero => simp only [List.length_cons] at enoughFirst; omega
          | succ first => cases second with
              | zero => simp only [List.length_cons] at enoughSecond; omega
              | succ second =>
                  cases found : lookup key store with
                  | none => simp only [evaluateFuel, found]
                  | some template =>
                      obtain ⟨actual, body⟩ := template
                      by_cases matching : actual = demand ∧ PhaseRechecking.checkOwners before (key.owner :: demand) = true ∧
                          (OwnerPhases.consume key.owner (nearer ++ receiving)).isSome = true
                      · have checked := matching.2.1
                        have selected := matching.2.2
                        have same := matching.1
                        subst actual
                        have smallerBound : demand.length < bound := by simp only [List.length_cons] at bounded; omega
                        have next := smaller demand.length smallerBound body (Nat.le_refl _)
                          first second (by simp only [List.length_cons] at enoughFirst; omega)
                          (by simp only [List.length_cons] at enoughSecond; omega)
                          store (nearer ++ receiving) (spend before key.owner)
                        simpa only [evaluateFuel, found, checked, selected, and_self, if_true] using next
                      · simp only [evaluateFuel, found, matching, if_false]
      | sequence firstBody secondBody ihFirst ihSecond =>
          intro bounded first second enoughFirst enoughSecond store receiving before
          have lengths := bounded
          simp only [List.length_append] at lengths enoughFirst enoughSecond
          simp only [evaluateFuel,
            ihFirst (by omega) first second (by omega) (by omega) store receiving before,
            ihSecond (by omega) first second (by omega) (by omega) store receiving (spendAll before _)]
      | emitAfter body nearer raw ih =>
          intro bounded first second enoughFirst enoughSecond store receiving before
          simp only [evaluateFuel, ih bounded first second enoughFirst enoughSecond store receiving before]
      | choice firstBody secondBody same ihFirst ihSecond =>
          intro bounded first second enoughFirst enoughSecond store receiving before
          have equal := same.length_eq
          simp only [evaluateFuel,
            ihFirst bounded first second enoughFirst enoughSecond store receiving before,
            ihSecond (by omega) first second (by omega) (by omega) store receiving before]

theorem fuel_stable (requirements : Requirements owners) (enoughFirst : owners.length ≤ first)
    (enoughSecond : owners.length ≤ second) :
    evaluateFuel first store receiving before requirements = evaluateFuel second store receiving before requirements :=
  fuel_stable_bound owners.length requirements (Nat.le_refl _) first second enoughFirst enoughSecond store receiving before

theorem evaluate_sequence {first : Requirements a} {second : Requirements b} :
    evaluate store receiving before (.sequence first second) =
      merge (evaluate store receiving before first) (evaluate store receiving (spendAll before a) second) := by
  simp only [evaluate, evaluateFuel]
  rw [fuel_stable first (by simp) (Nat.le_refl a.length), fuel_stable second (by simp) (Nat.le_refl b.length)]

theorem evaluate_emit {body : Requirements owners} :
    evaluate store receiving before (.emitAfter body nearer raw) =
      merge (evaluate store receiving before body) (OwnerSource.exportAt (nearer ++ receiving) (spendAll before owners) raw) := by
  simp only [evaluate, evaluateFuel]

theorem evaluate_choice {first : Requirements a} {second : Requirements b} :
    evaluate store receiving before (.choice first second same) =
      merge (evaluate store receiving before first) (evaluate store receiving before second) := by
  have equal := same.length_eq
  simp only [evaluate, evaluateFuel]
  rw [fuel_stable second (by omega) (Nat.le_refl b.length)]

theorem evaluate_invoke (known : lookup key store = some ⟨demand, body⟩) :
    evaluate store receiving before (.invoke key demand nearer) =
      if PhaseRechecking.checkOwners before (key.owner :: demand) = true ∧
          (OwnerPhases.consume key.owner (nearer ++ receiving)).isSome = true then
        evaluate store (nearer ++ receiving) (spend before key.owner) body else none := by
  simp only [evaluate, List.length_cons, evaluateFuel, known, true_and]

inductive Checked (store : Store) : OwnerPhases.Context →
    {owners : List Nat} → Phases → Requirements owners → Footprint → Prop where
  | request (exported : OwnerSource.exportAt (nearer ++ receiving) before raw = some row) :
      Checked store receiving before (.request nearer raw) row
  | retire (available : before owner = .available) : Checked store receiving before (.retire owner) []
  | spent (consumed : before owner = .consumed) : Checked store receiving before (.spent owner) []
  | invoke (known : lookup key store = some ⟨demand, body⟩)
      (ownersReady : PhaseRechecking.checkOwners before (key.owner :: demand) = true)
      (selection : OwnerPhases.Consumes key.owner (nearer ++ receiving) waiting)
      (next : Checked store (nearer ++ receiving) (spend before key.owner) body row) :
      Checked store receiving before (.invoke key demand nearer) row
  | sequence {a : Requirements firstOwners} {b : Requirements secondOwners}
      (first : Checked store receiving before a firstRow)
      (second : Checked store receiving (spendAll before firstOwners) b secondRow) :
      Checked store receiving before (@Requirements.sequence firstOwners secondOwners a b) (firstRow ++ secondRow)
  | emitAfter {requirements : Requirements owners}
      (body : Checked store receiving before requirements bodyRow)
      (exported : OwnerSource.exportAt (nearer ++ receiving) (spendAll before owners) raw = some requestRow) :
      Checked store receiving before (@Requirements.emitAfter owners requirements nearer raw) (bodyRow ++ requestRow)
  | choice (first : Checked store receiving before a firstRow)
      (second : Checked store receiving before b secondRow) :
      Checked store receiving before (.choice a b same) (firstRow ++ secondRow)

theorem checked_complete (checked : Checked store receiving before requirements row) :
    evaluate store receiving before requirements = some row := by
  induction checked with
  | request exported => simpa only [evaluate, evaluateFuel] using exported
  | retire ready => simp [evaluate, evaluateFuel, PhaseRechecking.checkOwners, ready]
  | spent consumed => simp [evaluate, evaluateFuel, consumed]
  | invoke known ready selection next ih =>
      simp only [evaluate_invoke known, ready, OwnerPhases.consumes_sound selection, Option.isSome_some,
        and_self, if_true, ih]
  | sequence first second ihFirst ihSecond => simp only [evaluate_sequence, ihFirst, ihSecond, merge]
  | emitAfter body exported ih => simp only [evaluate_emit, ih, exported, merge]
  | choice first second ihFirst ihSecond => simp only [evaluate_choice, ihFirst, ihSecond, merge]

theorem evaluator_layer_sound {requirements : Requirements owners}
    (invocations : ∀ key demand nearer receiving before row,
      evaluateFuel fuel store receiving before (.invoke key demand nearer) = some row →
        Checked store receiving before (.invoke key demand nearer) row)
    (checked : evaluateFuel fuel store receiving before requirements = some row) :
    Checked store receiving before requirements row := by
  induction requirements generalizing receiving before row with
  | request nearer raw => exact .request (by simpa only [evaluateFuel] using checked)
  | retire owner =>
      simp only [evaluateFuel] at checked
      split at checked
      · have ready : before owner = .available := by
          have good : PhaseRechecking.checkOwners before [owner] = true := by assumption
          simpa [PhaseRechecking.checkOwners] using good
        cases Option.some.inj checked
        exact .retire ready
      · cases checked
  | spent owner =>
      simp only [evaluateFuel] at checked
      split at checked
      · cases Option.some.inj checked
        exact .spent (by assumption)
      · cases checked
  | invoke key demand nearer => exact invocations key demand nearer receiving before row checked
  | sequence first second ihFirst ihSecond =>
      obtain ⟨a, b, checkedFirst, checkedSecond, rfl⟩ := PhaseRechecking.merge_split (by simpa only [evaluateFuel] using checked)
      exact .sequence (ihFirst checkedFirst) (ihSecond checkedSecond)
  | emitAfter body nearer raw ih =>
      obtain ⟨a, b, checkedBody, exported, rfl⟩ := PhaseRechecking.merge_split (by simpa only [evaluateFuel] using checked)
      exact .emitAfter (ih checkedBody) exported
  | choice first second same ihFirst ihSecond =>
      obtain ⟨a, b, checkedFirst, checkedSecond, rfl⟩ := PhaseRechecking.merge_split (by simpa only [evaluateFuel] using checked)
      exact .choice (ihFirst checkedFirst) (ihSecond checkedSecond)

theorem evaluateFuel_sound (fuel : Nat) {requirements : Requirements owners}
    (checked : evaluateFuel fuel store receiving before requirements = some row) :
    Checked store receiving before requirements row := by
  induction fuel generalizing owners receiving before row with
  | zero =>
      apply evaluator_layer_sound (fuel := 0) ?_ checked
      intro key demand nearer receiving before row checkedCall
      simp only [evaluateFuel] at checkedCall
      cases checkedCall
  | succ fuel ih =>
      apply evaluator_layer_sound (fuel := fuel + 1) ?_ checked
      intro key demand nearer receiving before row checkedCall
      cases found : lookup key store with
      | none => simp only [evaluateFuel, found] at checkedCall; cases checkedCall
      | some template =>
          obtain ⟨actual, body⟩ := template
          simp only [evaluateFuel, found] at checkedCall
          split at checkedCall
          · have matching : actual = demand ∧ PhaseRechecking.checkOwners before (key.owner :: demand) = true ∧
                (OwnerPhases.consume key.owner (nearer ++ receiving)).isSome = true := by assumption
            have same := matching.1
            have ready := matching.2.1
            have selected := matching.2.2
            subst actual
            cases selectedContext : OwnerPhases.consume key.owner (nearer ++ receiving) with
            | none => simp [selectedContext] at selected
            | some waiting => exact .invoke found ready (OwnerPhases.consumes_complete selectedContext) (ih checkedCall)
          · cases checkedCall

theorem evaluate_sound (checked : evaluate store receiving before requirements = some row) :
    Checked store receiving before requirements row := evaluateFuel_sound _ checked

theorem checked_iff : Checked store receiving before requirements row ↔ evaluate store receiving before requirements = some row :=
  ⟨checked_complete, evaluate_sound⟩

theorem checked_trace (checked : Checked store receiving before (owners := owners) requirements row) :
    Trace before owners (spendAll before owners) := by
  induction checked with
  | request | spent => exact .nil
  | retire ready => exact .cons ready .nil
  | invoke known ready selection next ih => exact PhaseRechecking.check_owners_iff.mp ready
  | sequence first second ihFirst ihSecond =>
      simpa only [PhaseRechecking.spendAll_append] using OwnerPhaseTransitions.trace_append ihFirst ihSecond
  | emitAfter body exported ih => exact ih
  | choice first second ihFirst ihSecond => exact ihFirst

theorem checked_once (checked : Checked store receiving before (owners := owners) requirements row) : owners.Nodup :=
  OwnerPhaseTransitions.trace_nodup (checked_trace checked)

theorem checked_sequence_parts {first : Requirements a} {second : Requirements b}
    (checked : Checked store receiving before (.sequence first second) row) :
    ∃ firstRow secondRow, Checked store receiving before first firstRow ∧
      Checked store receiving (spendAll before a) second secondRow ∧ row = firstRow ++ secondRow := by
  have evaluated := checked_complete checked
  rw [evaluate_sequence] at evaluated
  obtain ⟨firstRow, secondRow, checkedFirst, checkedSecond, same⟩ := PhaseRechecking.merge_split evaluated
  exact ⟨firstRow, secondRow, evaluate_sound checkedFirst, evaluate_sound checkedSecond, same⟩

/-- Successful invocation includes the active selection and the checked body;
    lookup provenance is supplied by the source-derived store. -/
theorem checked_invocation (checked : Checked store receiving before (.invoke key demand nearer) row) :
    ∃ body waiting, lookup key store = some ⟨demand, body⟩ ∧
      PhaseRechecking.checkOwners before (key.owner :: demand) = true ∧
      OwnerPhases.Consumes key.owner (nearer ++ receiving) waiting ∧
      Checked store (nearer ++ receiving) (spend before key.owner) body row := by
  have evaluated := checked_complete checked
  simp only [evaluate, List.length_cons, evaluateFuel] at evaluated
  cases found : lookup key store with
  | none => simp [found] at evaluated
  | some template =>
      obtain ⟨actual, body⟩ := template
      simp only [found] at evaluated
      split at evaluated
      · have matching : actual = demand ∧ PhaseRechecking.checkOwners before (key.owner :: demand) = true ∧
            (OwnerPhases.consume key.owner (nearer ++ receiving)).isSome = true := by assumption
        have same := matching.1
        have ready := matching.2.1
        have selected := matching.2.2
        subst actual
        cases selectedContext : OwnerPhases.consume key.owner (nearer ++ receiving) with
        | none => simp [selectedContext] at selected
        | some waiting =>
            exact ⟨body, waiting, rfl, ready, OwnerPhases.consumes_complete selectedContext,
              evaluate_sound evaluated⟩
      · cases evaluated

theorem invocation_unselectable
    (absent : OwnerPhases.consume key.owner (nearer ++ receiving) = none) :
    evaluate store receiving before (.invoke key demand nearer) = none := by
  simp only [evaluate, List.length_cons, evaluateFuel]
  cases found : lookup key store with
  | none => rfl
  | some template => obtain ⟨actual, body⟩ := template; simp [absent]

theorem evaluateFuel_prepend (requirements : Requirements owners) :
    evaluateFuel fuel store receiving before (requirements.prepend prefixContext) =
      evaluateFuel fuel store (prefixContext ++ receiving) before requirements := by
  induction requirements generalizing before with
  | request => simp only [Requirements.prepend, evaluateFuel, List.append_assoc]
  | retire | spent => simp only [Requirements.prepend, evaluateFuel]
  | invoke key demand nearer =>
      cases fuel <;> simp only [Requirements.prepend, evaluateFuel, List.append_assoc]
  | sequence first second ihFirst ihSecond => simp only [Requirements.prepend, evaluateFuel, ihFirst, ihSecond]
  | emitAfter body nearer raw ih => simp only [Requirements.prepend, evaluateFuel, ih, List.append_assoc]
  | choice first second same ihFirst ihSecond => simp only [Requirements.prepend, evaluateFuel, ihFirst, ihSecond]

theorem evaluate_prepend (requirements : Requirements owners) :
    evaluate store receiving before (requirements.prepend prefixContext) =
      evaluate store (prefixContext ++ receiving) before requirements := evaluateFuel_prepend requirements

theorem checked_prepend_iff :
    Checked store receiving before (requirements.prepend prefixContext) row ↔
      Checked store (prefixContext ++ receiving) before requirements row := by
  rw [checked_iff, evaluate_prepend, checked_iff]

namespace Examples
open OwnerPhaseTransitions (available empty)
open Ash.OneShot.SharedResumption.NestedExamples (outerBoundary outerWaiting innerBoundary innerWaiting innerCapture contracts)
open Ash.OneShot.SharedResumption.Examples (raw operations policy tables originalReceiver outside)

abbrev outerKey : Key := ⟨19, .resume⟩
abbrev innerKey : Key := ⟨29, .resume⟩
def inner : Requirements [] := .request [] raw
def outer : Requirements [29] :=
  .sequence (.invoke innerKey [] (OwnerPhases.ofStack tables innerBoundary)) (.spent 29)
def store : Store := [(outerKey, ⟨[29], outer⟩), (innerKey, ⟨[], inner⟩)]
def invocation : Requirements [19, 29] := .invoke outerKey [29] []

theorem outer_known : lookup outerKey store = some ⟨[29], outer⟩ := by rfl
theorem inner_known : lookup innerKey store = some ⟨[], inner⟩ := by rfl

theorem inner_evaluation : evaluate store receiving before inner = OwnerSource.exportAt receiving before raw := by
  simp only [inner, evaluate, evaluateFuel, List.nil_append]

theorem inner_invocation :
    evaluate store receiving before (.invoke innerKey [] nearer) =
      if PhaseRechecking.checkOwners before [29] = true ∧
          (OwnerPhases.consume 29 (nearer ++ receiving)).isSome = true then
        OwnerSource.exportAt (nearer ++ receiving) (spend before 29) raw else none := by
  rw [evaluate_invoke inner_known, inner_evaluation]

theorem outer_evaluation : evaluate store receiving before outer =
    if PhaseRechecking.checkOwners before [29] = true ∧
        (OwnerPhases.consume 29 (OwnerPhases.ofStack tables innerBoundary ++ receiving)).isSome = true then
      OwnerSource.exportAt (OwnerPhases.ofStack tables innerBoundary ++ receiving) (spend before 29) raw else none := by
  rw [outer, evaluate_sequence, inner_invocation]
  simp only [evaluate, evaluateFuel, spendAll, OwnerPhaseTransitions.spend_self, if_true]
  cases exported : OwnerSource.exportAt (OwnerPhases.ofStack tables innerBoundary ++ receiving) (spend before 29) raw <;>
    split <;> simp_all [merge]

theorem nested_edge : Edge store outerKey innerKey :=
  .linked outer_known (.first .here) inner_known

theorem nested_rank : rank store innerKey < rank store outerKey := edge_decreases nested_edge

theorem historical_outer_row : evaluate store (OwnerPhases.ofStack tables originalReceiver) (available [29]) outer = some [] := by
  rw [outer_evaluation]
  decide

theorem current_outer_row : evaluate store (OwnerPhases.ofStack tables outerWaiting) (available [29]) outer = some raw := by
  rw [outer_evaluation]
  decide

theorem recursive_invocation_row :
    evaluate store (OwnerPhases.ofStack tables outerBoundary) (available [19, 29]) invocation = some raw := by
  rw [invocation, evaluate_invoke outer_known]
  simp only [List.nil_append, outer_evaluation]
  decide

theorem recursive_invocation_checked :
    Checked store (OwnerPhases.ofStack tables outerBoundary) (available [19, 29]) invocation raw :=
  evaluate_sound recursive_invocation_row

theorem recursive_invocation_rejects_empty_outside :
    checkResidual [] (evaluate store (OwnerPhases.ofStack tables outerBoundary) (available [19, 29]) invocation) = false := by
  rw [recursive_invocation_row]
  decide

theorem recursive_invocation_accepts_declared_outside :
    checkResidual outside (evaluate store (OwnerPhases.ofStack tables outerBoundary) (available [19, 29]) invocation) = true := by
  rw [recursive_invocation_row]
  decide

theorem cached_outer_check_missed_request :
    SharedResumption.NestedExamples.outerRequirements.evaluate
        (OwnerPhases.ofStack tables outerWaiting) (available [29]) = some [] ∧
    evaluate store (OwnerPhases.ofStack tables outerWaiting) (available [29]) outer = some raw ∧ raw ≠ [] :=
  ⟨SharedResumption.NestedExamples.outer_check_passes, current_outer_row, by decide⟩

theorem inner_reconstructs_shared
    (checked : evaluate store (OwnerPhases.ofStack tables receiver) phases inner = some row) :
    SharedSourceSegments.Segment operations policy contracts tables [] receiver innerCapture
      phases .unit phases .unit [] row := by
  apply SharedResumption.Examples.captured_at_receiver
  simpa only [inner, evaluate, evaluateFuel, List.nil_append] using checked

theorem recursive_inner_source :
    SharedSourceSegments.Segment operations policy contracts tables [] innerWaiting innerCapture
      empty .unit empty .unit [] raw := inner_reconstructs_shared (by simp only [evaluate, evaluateFuel, inner]; decide)

theorem inner_template_demand : ([] : List Nat) = SharedResumption.NestedExamples.inner.resumeDemand := rfl
theorem outer_template_demand : [29] = SharedResumption.NestedExamples.outer.resumeDemand := rfl

theorem original_outer_source : SharedSourceSegments.Segment operations policy contracts tables [] originalReceiver
    SharedResumption.NestedExamples.outerCapture (available [29]) .unit empty .unit [29] [] :=
  SharedResumption.NestedExamples.outer_saved

theorem missing_template_rejected :
    evaluate [] (OwnerPhases.ofStack tables outerBoundary) (available [19, 29]) invocation = none := by
  simp only [invocation, evaluate, List.length_cons, List.length_nil, evaluateFuel, lookup]

def mismatched : Store := [(outerKey, ⟨[], inner⟩)]

theorem mismatched_demand_rejected :
    evaluate mismatched (OwnerPhases.ofStack tables outerBoundary) (available [19, 29]) invocation = none := by
  simp only [invocation, evaluate, List.length_cons, List.length_nil, evaluateFuel, mismatched, lookup]
  decide

def cyclic : Store :=
  [(outerKey, ⟨[29], .invoke innerKey [] []⟩), (innerKey, ⟨[19], .invoke outerKey [] []⟩)]

theorem inconsistent_cycle_rejected : evaluate cyclic [.live 19 false, .live 29 false] (available [19, 29]) invocation = none := by
  have first : lookup outerKey cyclic = some ⟨[29], Requirements.invoke innerKey [] []⟩ := rfl
  rw [invocation, evaluate_invoke first, if_pos (by decide)]
  simp only [evaluate, List.length_cons, List.length_nil, evaluateFuel, cyclic, lookup, outerKey, innerKey]
  decide

theorem no_authenticated_cycle : ¬ Relation.TransGen (Edge cyclic) outerKey outerKey := no_cycle

theorem double_invocation_rejected :
    evaluate store (OwnerPhases.ofStack tables innerBoundary) (available [29]) (.sequence (.invoke innerKey [] []) (.invoke innerKey [] [])) = none := by
  rw [evaluate_sequence, inner_invocation, inner_invocation]
  decide

theorem branch_alternatives_admitted :
    evaluate store (OwnerPhases.ofStack tables innerBoundary) (available [29]) (.choice (.invoke innerKey [] []) (.invoke innerKey [] []) (.refl _)) = some (raw ++ raw) := by
  rw [evaluate_choice, inner_invocation]
  decide

theorem unavailable_nested_owner_rejected :
    evaluate store (OwnerPhases.ofStack tables outerBoundary) (available [19]) invocation = none := by
  rw [invocation, evaluate_invoke outer_known]
  decide

theorem dormant_owner_is_owned : 29 ∈ ownedTickets outerBoundary := by decide

theorem dormant_owner_is_unselectable :
    OwnerPhases.consume 29 (OwnerPhases.ofStack tables outerBoundary) = none := rfl

theorem dormant_invocation_rejected :
    evaluate store (OwnerPhases.ofStack tables outerBoundary) (available (ownedTickets outerBoundary))
      (.invoke innerKey [] []) = none := invocation_unselectable dormant_owner_is_unselectable

theorem modes_are_distinct : lookup ⟨29, .dispose⟩ store = none := by decide

theorem spare_fuel_same_result :
    evaluateFuel 9 store (OwnerPhases.ofStack tables outerBoundary) (available [19, 29]) invocation = some raw := by
  rw [fuel_stable invocation (first := 9) (second := 2) (by decide) (by decide)]
  exact recursive_invocation_row

end Examples

end Ash.OneShot.RecursiveRequirements

#print axioms Ash.OneShot.RecursiveRequirements.call_decreases
#print axioms Ash.OneShot.RecursiveRequirements.edge_decreases
#print axioms Ash.OneShot.RecursiveRequirements.edge_not_self
#print axioms Ash.OneShot.RecursiveRequirements.path_decreases
#print axioms Ash.OneShot.RecursiveRequirements.no_cycle
#print axioms Ash.OneShot.RecursiveRequirements.invocation_wellFounded
#print axioms Ash.OneShot.RecursiveRequirements.fuel_stable_bound
#print axioms Ash.OneShot.RecursiveRequirements.fuel_stable
#print axioms Ash.OneShot.RecursiveRequirements.evaluate_sequence
#print axioms Ash.OneShot.RecursiveRequirements.evaluate_emit
#print axioms Ash.OneShot.RecursiveRequirements.evaluate_choice
#print axioms Ash.OneShot.RecursiveRequirements.evaluate_invoke
#print axioms Ash.OneShot.RecursiveRequirements.checked_complete
#print axioms Ash.OneShot.RecursiveRequirements.evaluator_layer_sound
#print axioms Ash.OneShot.RecursiveRequirements.evaluateFuel_sound
#print axioms Ash.OneShot.RecursiveRequirements.evaluate_sound
#print axioms Ash.OneShot.RecursiveRequirements.checked_iff
#print axioms Ash.OneShot.RecursiveRequirements.checked_trace
#print axioms Ash.OneShot.RecursiveRequirements.checked_once
#print axioms Ash.OneShot.RecursiveRequirements.checked_sequence_parts
#print axioms Ash.OneShot.RecursiveRequirements.checked_invocation
#print axioms Ash.OneShot.RecursiveRequirements.invocation_unselectable
#print axioms Ash.OneShot.RecursiveRequirements.evaluateFuel_prepend
#print axioms Ash.OneShot.RecursiveRequirements.evaluate_prepend
#print axioms Ash.OneShot.RecursiveRequirements.checked_prepend_iff
#print axioms Ash.OneShot.RecursiveRequirements.Examples.outer_known
#print axioms Ash.OneShot.RecursiveRequirements.Examples.inner_known
#print axioms Ash.OneShot.RecursiveRequirements.Examples.inner_evaluation
#print axioms Ash.OneShot.RecursiveRequirements.Examples.inner_invocation
#print axioms Ash.OneShot.RecursiveRequirements.Examples.outer_evaluation
#print axioms Ash.OneShot.RecursiveRequirements.Examples.nested_edge
#print axioms Ash.OneShot.RecursiveRequirements.Examples.nested_rank
#print axioms Ash.OneShot.RecursiveRequirements.Examples.historical_outer_row
#print axioms Ash.OneShot.RecursiveRequirements.Examples.current_outer_row
#print axioms Ash.OneShot.RecursiveRequirements.Examples.recursive_invocation_row
#print axioms Ash.OneShot.RecursiveRequirements.Examples.recursive_invocation_checked
#print axioms Ash.OneShot.RecursiveRequirements.Examples.recursive_invocation_rejects_empty_outside
#print axioms Ash.OneShot.RecursiveRequirements.Examples.recursive_invocation_accepts_declared_outside
#print axioms Ash.OneShot.RecursiveRequirements.Examples.cached_outer_check_missed_request
#print axioms Ash.OneShot.RecursiveRequirements.Examples.inner_reconstructs_shared
#print axioms Ash.OneShot.RecursiveRequirements.Examples.recursive_inner_source
#print axioms Ash.OneShot.RecursiveRequirements.Examples.inner_template_demand
#print axioms Ash.OneShot.RecursiveRequirements.Examples.outer_template_demand
#print axioms Ash.OneShot.RecursiveRequirements.Examples.original_outer_source
#print axioms Ash.OneShot.RecursiveRequirements.Examples.missing_template_rejected
#print axioms Ash.OneShot.RecursiveRequirements.Examples.mismatched_demand_rejected
#print axioms Ash.OneShot.RecursiveRequirements.Examples.inconsistent_cycle_rejected
#print axioms Ash.OneShot.RecursiveRequirements.Examples.no_authenticated_cycle
#print axioms Ash.OneShot.RecursiveRequirements.Examples.double_invocation_rejected
#print axioms Ash.OneShot.RecursiveRequirements.Examples.branch_alternatives_admitted
#print axioms Ash.OneShot.RecursiveRequirements.Examples.unavailable_nested_owner_rejected
#print axioms Ash.OneShot.RecursiveRequirements.Examples.dormant_owner_is_owned
#print axioms Ash.OneShot.RecursiveRequirements.Examples.dormant_owner_is_unselectable
#print axioms Ash.OneShot.RecursiveRequirements.Examples.dormant_invocation_rejected
#print axioms Ash.OneShot.RecursiveRequirements.Examples.modes_are_distinct
#print axioms Ash.OneShot.RecursiveRequirements.Examples.spare_fuel_same_result
