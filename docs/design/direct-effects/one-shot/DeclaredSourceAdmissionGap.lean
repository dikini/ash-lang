import DeclaredSourceCapture
import ContextualClauseChecks

/-! A concrete admission gap: source typing and linear continuation use do not
certify an advertised effect row. The clause performs an operation before its
single resume, yet the earlier source-only Offer can advertise an empty row. This
is a counterexample to deriving the missing upper certificate from that source-only Offer alone,
not a claim that the unfinished admission judgment is already sound. -/
namespace Ash.OneShot.DeclaredSourceAdmissionGap
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts
open DeclaredSources (Expression)
open RecursiveRequirements (Requirements Store Checked evaluate)

def effect : Instance := .user 117 []
def operations : Operations := fun actual operation =>
  if actual = effect ∧ operation = 0 then some (.unit, .unit) else none
def policy : Syntax.TicketPolicy := fun _ => ⟨true, false⟩
def body : Code := .bind 7 (.perform (Instantiation.freezeEffect effect) 0 .unit) (.resume 9 .unit)
def requirements (owner : Nat) (contract : Owners.Contract) : Requirements (owner :: contract.resumeDemand) :=
  .sequence (.emitAfter (.request [] []) [] [⟨effect, 0, false⟩])
    (.sequence (.request [] []) (.invoke ⟨owner, .resume⟩ contract.resumeDemand []))

theorem body_source (base : Owners.Contracts) (contract : Owners.Contract)
    (inputSame : contract.input = .unit) (answerSame : contract.answer = .unit) (resumeBound : contract.resumeEffects ⊆ [effect]) :
    Expression operations policy (base.insert owner contract) [] [effect] (.ticket 9 owner)
      environment body contract.answer (owner :: contract.resumeDemand) (requirements owner contract) := by
  have known : (base.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
  have operationKnown : operations effect 0 = some (.unit, .unit) := by decide
  have operand : Expression operations policy (base.insert owner contract) [] [effect] (.ticket 9 owner)
      (environment.extend 7 .unit) .unit contract.input [] (.request [] []) := inputSame.symm ▸ .stable .unit
  unfold body requirements
  exact Expression.bind (.perform operationKnown List.mem_cons_self (.stable .unit)
      (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]))
    (.resume (binder := 9) known (by rfl) (by rfl) operand
      resumeBound
      (by simp [answerSame, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]))

theorem empty_advertisement (base : Owners.Contracts) :
    SourceClauseDeclarations.SourceOffer operations policy base [] environment [effect] 1 9 .unit .unit .unit [] [] body false (some []) := by
  apply SourceClauseDeclarations.SourceOffer.available
  intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
  exact ⟨_, _, DeclaredSources.expression_erase
    (answerSame ▸ body_source base contract inputSame answerSame (by rw [resumeSame]; exact List.nil_subset _))⟩

/-- Matching the continuation interface does not itself certify the clause's
advertised footprint. The earlier source-only offer still accepts this body. -/
theorem matching_empty_advertisement (base : Owners.Contracts) :
    SourceClauseDeclarations.SourceOffer operations policy base [] environment [effect]
      1 9 .unit .unit .unit [effect] [] body false (some []) := by
  apply SourceClauseDeclarations.SourceOffer.available
  intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
  exact ⟨_, _, DeclaredSources.expression_erase
    (answerSame ▸ body_source base contract inputSame answerSame (resumeSame.symm ▸ List.Subset.refl _))⟩

theorem linear_body : Uses policy (.ticket 9 (policy 9)) .available body .consumed :=
  .bind (.perform .unit) (.resume rfl .unit)

def contract : Owners.Contract := ⟨.unit, .unit, false, [], [], [], none, [], []⟩
def store : Store := [(⟨0, .resume⟩, ⟨[], .request [] []⟩),
  (⟨0, .dispose⟩, ⟨[], .request [] []⟩)]
def receiving : OwnerPhases.Context := [.live 0 false]
def before : OwnerPhaseTransitions.Phases := OwnerPhaseTransitions.available [0]

/-- The rejection below uses records from actual structurally typed source. -/
theorem store_source (effects : List Instance := []) :
    ClauseRowAdmission.SourceStore operations 0 { contract with resumeEffects := effects } store := by
  let actual := { contract with resumeEffects := effects }
  let contracts : Owners.Contracts := fun _ => some actual
  let tables : CallableProtectionFrames.Tables := fun _ => []
  let stack : Stack := .live 0 .unit .unit .nil .none .nil
  have source : SourceTemplates.Segment operations policy contracts tables [] stack .unit .unit []
      (.sequence (.spent 0) (.request [] [])) [(⟨0, .resume⟩, ⟨[], .request [] []⟩)] :=
    SourceTemplates.Segment.live (contracts := contracts) (contract := actual)
      (caller := .none) rfl rfl rfl ⟨.none, .none⟩ rfl .nil .nil
  have closing : RecursiveRecords.Records operations policy contracts tables [] stack
      [(⟨0, .dispose⟩, ⟨[], .request [] []⟩)] :=
    .close rfl .nil .nil .nil .nil
  exact ClauseRowAdmission.SourceStore.of_source source closing rfl

theorem actual_check : Checked store receiving before (requirements 0 contract) [⟨effect, 0, false⟩] := by
  apply Checked.sequence (firstRow := [⟨effect, 0, false⟩]) (secondRow := [])
  · apply Checked.emitAfter (bodyRow := []) (requestRow := [⟨effect, 0, false⟩])
    · exact .request (by rfl)
    · rfl
  · apply Checked.sequence (firstRow := []) (secondRow := [])
    · exact .request (by rfl)
    · exact .invoke (by rfl) (by rfl) .hit (.request (by rfl))

theorem empty_upper_impossible :
    ¬ ∃ upperStore upperRequirements,
      RecursiveBounds.StoreBounds store upperStore ∧
      RecursiveBounds.Bounds (requirements 0 contract) upperRequirements ∧
      Checked upperStore receiving before upperRequirements [] := by
  rintro ⟨upperStore, upperRequirements, stores, bounds, checked⟩
  obtain ⟨row, lower, covered⟩ := RecursiveBounds.checked_below checked stores bounds
  have same := Option.some.inj ((RecursiveRequirements.checked_complete lower).symm.trans
    (RecursiveRequirements.checked_complete actual_check))
  rw [same] at covered
  exact List.not_mem_nil (covered List.mem_cons_self)

/-- Opening a check into explicit invocation assumptions cannot hide the
literal operation. This rejects the empty advertisement for this exact source
requirement, without assuming completeness of declaration admission. -/
theorem empty_contextual_certificate_impossible :
    ¬ ∃ row calls,
      ContextualClauseChecks.Derivation receiving before (requirements 0 contract) row calls ∧
      (∀ call ∈ calls, call.Check store) ∧ EffectBounds.Covers [] row := by
  rintro ⟨row, calls, derived, supplied, covered⟩
  have checked := ContextualClauseChecks.close derived supplied
  have same := Option.some.inj ((RecursiveRequirements.checked_complete checked).symm.trans
    (RecursiveRequirements.checked_complete actual_check))
  rw [same] at covered
  exact List.not_mem_nil (covered List.mem_cons_self)

/-- The request cannot disappear by choosing another source derivation for
the same body. Reuse request evaluation rather than prove syntax uniqueness. -/
theorem every_body_check_contains_effect
    (source : Expression operations policy contracts world allowed scope environment body answer demand tree)
    (checked : Checked store receiving before tree row) : ⟨effect, 0, false⟩ ∈ row := by
  unfold body at source
  cases source with
  | stable summary => cases summary with
    | bind first last => cases last
  | callable summary => cases summary with
    | summaryBind first last => cases last
  | bind first last =>
      obtain ⟨firstRow, lastRow, firstCheck, lastCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
      have evaluated := RecursiveDispatch.request_evaluation (records := store) (receiving := receiving) (before := before)
        (DeclaredSources.expression_erase first) (by trivial)
      have exactRow : firstRow = [⟨effect, 0, false⟩] :=
        Option.some.inj ((RecursiveRequirements.checked_complete firstCheck).symm.trans evaluated)
      rw [same, exactRow]
      exact List.mem_append_left _ List.mem_cons_self

/-- Even with a matching resume interface, the stronger declaration rejects
the false footprint advertisement for every source requirement witness. -/
theorem empty_admitted_offer_rejected (fresh : base 0 = none) :
    ¬ DeclaredSources.Offer operations policy base [] environment [effect] 1 9 .unit .unit .unit [effect] [] body false false (some []) := by
  intro admitted
  cases admitted with
  | available resumeInterface closeInterface family =>
      let aligned : Owners.Contract := { contract with resumeEffects := [effect] }
      have supplied := family 0 aligned fresh rfl rfl rfl rfl rfl (List.Perm.refl [])
      cases supplied with
      | typed source rows =>
          have interface : ClauseRowAdmission.Interface 0 aligned false store [] before [] := by
            refine ⟨?_, ?_, ?_, ?_, by simp [OwnerPhaseTransitions.liveNames]⟩
            · exact .invoke (by rfl) (by rfl) .hit (.request (by rfl))
            · intro _ row same; cases same
            · intro impossible; cases impossible
            · intro _ row same; cases same
          obtain ⟨row, checked, covered⟩ := rows.instantiate interface (by rfl) (store_source [effect])
          exact List.not_mem_nil (covered (every_body_check_contains_effect source checked))

end Ash.OneShot.DeclaredSourceAdmissionGap

#print axioms Ash.OneShot.DeclaredSourceAdmissionGap.body_source
#print axioms Ash.OneShot.DeclaredSourceAdmissionGap.empty_advertisement
#print axioms Ash.OneShot.DeclaredSourceAdmissionGap.matching_empty_advertisement
#print axioms Ash.OneShot.DeclaredSourceAdmissionGap.linear_body
#print axioms Ash.OneShot.DeclaredSourceAdmissionGap.actual_check
#print axioms Ash.OneShot.DeclaredSourceAdmissionGap.empty_upper_impossible
#print axioms Ash.OneShot.DeclaredSourceAdmissionGap.empty_contextual_certificate_impossible
#print axioms Ash.OneShot.DeclaredSourceAdmissionGap.every_body_check_contains_effect
#print axioms Ash.OneShot.DeclaredSourceAdmissionGap.empty_admitted_offer_rejected

#print axioms Ash.OneShot.DeclaredSourceAdmissionGap.store_source
