import SourceTemplates

/-! Source extraction and caller reinterpretation for ordinary requirements. -/
namespace Ash.OneShot.RecursiveOutward
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements Checked evaluate)
open OwnerPhaseTransitions (Phases spendAll project)
open SourceTemplates (Expression)

theorem expression_outward
    (source : Expression operations policy contracts world allowed scope environment code output demand requirements)
    (empty : scope = .none) : ∃ row, Outward requirements row := by
  induction source using Expression.rec (motive_2 := fun _ _ _ _ _ _ _ => True) with
  | stable summary | callable summary ih => exact ⟨_, Outward.request (layers := [])⟩
  | lambda body outward formed ih => exact ⟨_, Outward.request (layers := [])⟩
  | purePair left right ihLeft ihRight => exact ⟨_, Outward.request (layers := [])⟩
  | pair left right ihLeft ihRight | bind left right ihLeft ihRight =>
      obtain ⟨a, first⟩ := ihLeft empty
      obtain ⟨b, second⟩ := ihRight empty
      exact ⟨_, .sequence first second⟩
  | app function argument admitted ihFunction ihArgument | cleanup function argument admitted ihFunction ihArgument =>
      obtain ⟨a, first⟩ := ihFunction empty
      obtain ⟨b, second⟩ := ihArgument empty
      exact ⟨_, .emitAfter (layers := []) (.sequence first second)⟩
  | branch condition yes no same ihCondition ihYes ihNo =>
      obtain ⟨a, first⟩ := ihCondition empty
      obtain ⟨b, second⟩ := ihYes empty
      obtain ⟨c, third⟩ := ihNo empty
      exact ⟨_, .sequence first (.choice second third)⟩
  | perform known admitted operand formed ih =>
      obtain ⟨row, current⟩ := ih empty
      exact ⟨_, .emitAfter (layers := []) current⟩
  | handler body clauses capabilities coverage unique admitted table modes ih =>
      obtain ⟨row, current⟩ := ih empty
      exact ⟨_, prepend current [_]⟩
  | resume known resolved permission operand admitted formed ih | discard known resolved permission unprotected admitted =>
      subst_vars
      cases resolved
  | resource initializer body formed effectsBound admitted outward ih ihBody =>
      obtain ⟨row, current⟩ := ih empty
      exact ⟨_, .emitAfter (layers := []) current⟩
  | scopedResource initializer body formed effectsBound admitted discharged ihInit ihBody =>
      obtain ⟨a, first⟩ := ihInit empty
      obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
      obtain ⟨b, opened⟩ := ihBody identity fresh empty
      obtain ⟨c, second⟩ := hidden (discharged identity fresh) opened
      exact ⟨_, .sequence first second⟩
  | _ => intros; trivial

theorem isolated_evaluation (source : Outward requirements row) :
    evaluate store [] before requirements = row := by
  rw [evaluation source]
  cases row <;> rfl

theorem unique (first : Outward requirements a) (second : Outward requirements b) : a = b :=
  (isolated_evaluation (store := []) (before := OwnerPhaseTransitions.empty) first).symm.trans
    (isolated_evaluation second)

theorem failed_summary_rejected (source : Outward requirements none) :
    ¬ Checked store receiving before requirements row := by
  intro checked
  have evaluated := RecursiveRequirements.checked_complete checked
  rw [evaluation source] at evaluated
  cases evaluated

/-- A successful source check fixes an outward row before interpreting any
    caller. The same row is reinterpreted under every other actual caller. -/
theorem checked_source_summary
    (source : Expression operations policy contracts world allowed .none environment code output demand requirements)
    (checked : Checked store receiving before requirements row) :
    ∃ raw, Outward requirements (some raw) ∧ demand = [] ∧
      OwnerSource.exportAt receiving before raw = some row ∧
      ∀ nextStore nextReceiving nextPhases nextRow,
        Checked nextStore nextReceiving nextPhases requirements nextRow ↔
          OwnerSource.exportAt nextReceiving nextPhases raw = some nextRow := by
  obtain ⟨summary, derived⟩ := expression_outward source rfl
  cases summary with
  | none => exact False.elim (failed_summary_rejected derived checked)
  | some raw =>
      have agreement := evaluation derived store receiving before
      have original := RecursiveRequirements.checked_complete checked
      rw [agreement] at original
      refine ⟨raw, derived, no_owners derived, original, ?_⟩
      intro nextStore nextReceiving nextPhases nextRow
      rw [RecursiveRequirements.checked_iff, evaluation derived]
      rfl

/-- Reuse uniform residual coverage to check an actual body beneath an
    advertised outward bound in the same ordered receiving context. -/
theorem checked_from_bound (source : Outward requirements (some actual))
    (covered : actual ⊆ bound)
    (accepted : OwnerSource.exportAt receiving before bound = some exported) :
    ∃ row, Checked store receiving before requirements row ∧ row ⊆ exported := by
  obtain ⟨row, evaluated, bounded⟩ := UniformClauseBounds.residual_coverage covered accepted
  refine ⟨row, RecursiveRequirements.evaluate_sound ?_, bounded⟩
  rw [evaluation source]
  exact evaluated

namespace Examples

def effect : Instance := .user 91 []
def other : Instance := .user 92 []
def request : Footprint := [⟨effect, 0, false⟩]
def exposed : Footprint := [⟨other, 0, false⟩]
def interpreters : ProtectionContracts.Context := [.handler effect 0 [(0, ⟨false, some exposed, some exposed⟩)]]
def requirements : Requirements [] := .request (interpreters.map OwnerPhases.Entry.ordinary) request

theorem local_handler_summary : Outward requirements (some exposed) := by
  have result : residualize interpreters request = some exposed := by decide
  exact result ▸ Outward.request (layers := interpreters) (raw := request)

theorem different_callers_reinterpret :
    evaluate [] [.ordinary (.handler other 1 [(0, ⟨false, some [], some []⟩)])] OwnerPhaseTransitions.empty requirements = some [] ∧
    evaluate [] [] OwnerPhaseTransitions.empty requirements = some exposed := by
  constructor
  · rw [evaluation local_handler_summary]; decide
  · exact isolated_evaluation local_handler_summary

def invalid : Requirements [] := .request [.ordinary (.handler effect 0 [])] request

theorem missing_local_clause : Outward invalid none := by
  have result : residualize [.handler effect 0 []] request = none := by decide
  exact result ▸ Outward.request (layers := [.handler effect 0 []]) (raw := request)

/-- An outer handler cannot repair a missing operation in the nearer exact
    interpretation. Failure and an empty outward row stay distinct. -/
theorem outer_handler_cannot_repair :
    ¬ Checked [] [.ordinary (.handler effect 1 [(0, ⟨false, some [], some []⟩)])]
      OwnerPhaseTransitions.empty invalid row := failed_summary_rejected missing_local_clause

end Examples

end Ash.OneShot.RecursiveOutward

#print axioms Ash.OneShot.RecursiveOutward.expression_outward
#print axioms Ash.OneShot.RecursiveOutward.isolated_evaluation
#print axioms Ash.OneShot.RecursiveOutward.unique
#print axioms Ash.OneShot.RecursiveOutward.failed_summary_rejected
#print axioms Ash.OneShot.RecursiveOutward.checked_source_summary
#print axioms Ash.OneShot.RecursiveOutward.checked_from_bound
#print axioms Ash.OneShot.RecursiveOutward.Examples.local_handler_summary
#print axioms Ash.OneShot.RecursiveOutward.Examples.different_callers_reinterpret
#print axioms Ash.OneShot.RecursiveOutward.Examples.missing_local_clause
#print axioms Ash.OneShot.RecursiveOutward.Examples.outer_handler_cannot_repair
